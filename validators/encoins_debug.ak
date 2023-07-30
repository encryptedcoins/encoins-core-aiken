use aiken/builtin.{
  add_integer, serialise_data, sha2_256, snd_pair, tail_list,
  verify_ed25519_signature,
}
use aiken/bytearray
use aiken/cbor
use aiken/dict.{from_list}
use aiken/list.{any, filter, foldr, length, map}
use aiken/math.{abs}
use aiken/string
use aiken/transaction.{InlineDatum, Mint, ScriptContext}
use aiken/transaction/credential.{Address}
use aiken/transaction/value.{
  Value, ada_asset_name, ada_policy_id, add, flatten, from_lovelace,
  from_minted_value, lovelace_of, merge, negate, policies, tokens, zero,
}
use encoins_core_aiken/value_extra.{isNonnegativeValue}

const minAdaTxOutInLedger = 2000000

const minMaxAdaTxOutInLedger = 1000000000

const depositMultiplier = 2

// Beacon token and verifierPKH
type EncoinsPolicyParams =
  (Value, ByteArray)

// Ledger address, change address, total fees
type TxParams =
  (Address, Address, Int)

type EncoinsInputOnChain =
  (Int, List<(ByteArray, Int)>)

type ProofHash =
  ByteArray

type ProofSignature =
  ByteArray

type EncoinsRedeemerOnChain =
  (TxParams, EncoinsInputOnChain, ProofHash, ProofSignature)

fn hashRedeemer(red: EncoinsRedeemerOnChain) -> ByteArray {
  let (params, input, proofHash, _) = red
  sha2_256(serialise_data((params, input, proofHash)))
}

fn checkLedgerOuputValue1(vals: List<Value>) {
  when vals is {
    [] -> True
    [x, ..] ->
      length(flatten(x)) <= 2 && checkLedgerOuputValue2(tail_list(vals))
  }
}

fn checkLedgerOuputValue2(vals: List<Value>) {
  when vals is {
    [] -> True
    [x, ..] ->
      length(flatten(x)) == 2 && lovelace_of(x) == minAdaTxOutInLedger && checkLedgerOuputValue2(
        tail_list(vals),
      )
  }
}

fn traceOnFalse(msg: String, pred: Bool) -> Bool {
  when pred is {
    True -> True
    False -> {
      trace msg
      False
    }
  }
}

validator(par: EncoinsPolicyParams) {
  fn encoinsPolicyCheckDebug(
    red: EncoinsRedeemerOnChain,
    context: ScriptContext,
  ) -> Bool {
    // Destructuring arguments
    let info = context.transaction
    let vMint = from_minted_value(info.mint)
    expect Mint(encoinsSymb) = context.purpose
    let (beacon, verifierPKH) = par
    let ((ledgerAddr, changeAddr, feesWithSign), (v, inputs), _, sig) = red
    let fees = abs(feesWithSign)
    let val = from_lovelace(v * 1000000)
    let valFees = from_lovelace(fees * 1000000)
    let deposits =
      depositMultiplier * foldr(map(inputs, snd_pair), 0, add_integer)
    let valDeposits = from_lovelace(deposits * 1000000)
    let fromCondMsgs =
      fn(msgs) { foldr(msgs, @"", string.concat) }

    // Defining conditions
    // Condition 0
    let actual = tokens(vMint, encoinsSymb)
    let expected = from_list(inputs, bytearray.compare)
    let cond0 = actual == expected && policies(vMint) == [encoinsSymb]
    let cond0msgs =
      fromCondMsgs(
        [
          @"cond0:",
          @"actual: ",
          cbor.diagnostic(actual),
          @"expected: ",
          cbor.diagnostic(expected),
          @"policies: ",
          cbor.diagnostic(policies(vMint)),
        ],
      )

    // Condition 1
    let cond1 = verify_ed25519_signature(verifierPKH, hashRedeemer(red), sig)
    // Condition 2
    let refIns = map(info.reference_inputs, fn(x) { x.output })
    let cond2 =
      any(
        refIns,
        fn(o) {
          o.address == ledgerAddr && isNonnegativeValue(
            merge(o.value, negate(beacon)),
          )
        },
      )
    let cond2msgs =
      fromCondMsgs([@"cond2:", @"refIns:", cbor.diagnostic(refIns)])

    // Conditions 3 and 4
    let ins = map(info.inputs, fn(x) { x.output })
    let ledgerSpentOuts =
      filter(
        ins,
        fn(x) {
          x.address == ledgerAddr && isNonnegativeValue(
            add(x.value, ada_policy_id, ada_asset_name, -minAdaTxOutInLedger),
          )
        },
      )
    // vOuts are the values flowing out of the Ledger address
    let vOuts = map(ledgerSpentOuts, fn(x) { x.value })
    let vOut = foldr(vOuts, zero(), merge)

    let ledgerProducedOuts =
      filter(
        info.outputs,
        fn(x) {
          x.address == ledgerAddr && isNonnegativeValue(
            add(x.value, ada_policy_id, ada_asset_name, -minAdaTxOutInLedger),
          ) && x.datum == InlineDatum(Void)
        },
      )
    // vIns are the values flowing into the Ledger address
    let vIns = map(ledgerProducedOuts, fn(x) { x.value })
    let vIn = foldr(vIns, zero(), merge)

    // Wallet Mode
    let cond3 = vIn == merge(vOut, val)

    // Ledger Mode
    let cond4 = vIn == merge(vOut, merge(vMint, merge(val, valDeposits)))
    let cond3or4msgs =
      fromCondMsgs(
        [
          @"cond3:",
          @"vIn",
          cbor.diagnostic(vIn),
          @"vOutWithVal",
          cbor.diagnostic(merge(vOut, val)),
          @"cond4:",
          @"valDeposits",
          cbor.diagnostic(valDeposits),
          @"merge(vOut, merge(vMint, merge(val, valDeposits))) = ",
          cbor.diagnostic(merge(vMint, merge(val, valDeposits))),
        ],
      )

    let cond5msgs =
      fromCondMsgs(
        [
          @"cond5:",
          @"vIns",
          cbor.diagnostic(map(vIns, fn(x) { length(flatten(x)) })),
        ],
      )

    let cond5 = checkLedgerOuputValue1(vIns)

    // Condition 6
    let depositsOrZero =
      if cond4 {
        deposits
      } else {
        0
      }
    let valDepositsOrZero = from_lovelace(depositsOrZero * 1000000)

    let cond6msgs =
      fromCondMsgs(
        [
          @"cond6:",
          @"v + fees + depositsOrZero:",
          cbor.diagnostic(v + fees + depositsOrZero),
          @"merge(o.value, merge(val, merge(valFees, valDepositsOrZero)))",
          cbor.diagnostic(
            filter(info.outputs, fn(o) { o.address == changeAddr }),
          ),
          @"val=",
          cbor.diagnostic(val),
          @"valFees=",
          cbor.diagnostic(valFees),
          @"valDepositsOrZero=",
          cbor.diagnostic(valDepositsOrZero),
          @"deposits",
          cbor.diagnostic(deposits),
        ],
      )

    let cond6 =
      v + fees + depositsOrZero >= 0 || any(
        info.outputs,
        fn(o) {
          o.address == changeAddr && isNonnegativeValue(
            merge(o.value, merge(val, merge(valFees, valDepositsOrZero))),
          )
        },
      )
    // Condition 7
    let cond7 =
      length(filter(vIns, fn(x) { lovelace_of(x) >= minMaxAdaTxOutInLedger })) > 0

    // Imposing validation conditions
    traceOnFalse(cond0msgs, cond0) && traceOnFalse(@"cond1:", cond1) && traceOnFalse(
      cond2msgs,
      cond2,
    ) && traceOnFalse(cond3or4msgs, cond3 || cond4) && traceOnFalse(
      cond5msgs,
      cond5,
    ) && traceOnFalse(cond6msgs, cond6) && cond7
  }
}
