use aiken/builtin.{
  add_integer, serialise_data, sha2_256, snd_pair, tail_list,
  verify_ed25519_signature,
}
use aiken/bytearray
use aiken/cbor.{}
use aiken/dict.{from_list, has_key}
use aiken/list.{any, filter, foldr, length, map}
use aiken/math.{abs}
use aiken/string.{}
use aiken/transaction.{InlineDatum, Mint, ScriptContext}
use aiken/transaction/credential.{Address}
use aiken/transaction/value.{
  PolicyId, Value, ada_policy_id, ada_asset_name, add, flatten, from_lovelace, 
  from_minted_value, lovelace_of, merge, negate, policies, tokens, zero,
}
use encoins_core_aiken/value_extra.{isNonnegativeValue}

const minAdaTxOutInLedger =
  2000000

const depositMultiplier =
  2

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
  let (params, input, proofHash, _) =
    red
  sha2_256(serialise_data((params, input, proofHash)))
}

fn checkLedgerOuputValue1(vals: List<Value>) {
  when vals is {
    [] ->
      True
    [x, ..] ->
      length(flatten(x)) <= 2 && checkLedgerOuputValue2(tail_list(vals))
  }
}

fn checkLedgerOuputValue2(vals: List<Value>) {
  when vals is {
    [] ->
      True
    [x, ..] ->
      length(flatten(x)) == 2 && checkLedgerOuputValue2(tail_list(vals))
  }
}

fn traceOnFalse(msg : String, pred : Bool) -> Bool {
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
    let info =
      context.transaction
    let vMint =
      from_minted_value(info.mint)
    expect Mint(encoinsSymb) =
      context.purpose
    let (beacon, verifierPKH) =
      par
    let ((ledgerAddr, changeAddr, feesWithSign), (v, inputs), _, sig) =
      red
    let fees =
      abs(feesWithSign)
    let val =
      from_lovelace(v * 1000000)
    let valFees =
      from_lovelace(fees * 1000000)
    let deposits =
      depositMultiplier * foldr(map(inputs, snd_pair), 0, add_integer)
    let valDeposits =
      from_lovelace(deposits * 1000000)
    let minTxOutValueInLedger =
      from_lovelace(minAdaTxOutInLedger)
    let fromCondMsgs = 
        fn(msgs) {foldr(msgs, @"", string.concat)}

    // Defining conditions
    // Condition 0
    let actual =
      tokens(vMint, encoinsSymb)
    let expected =
      from_list(inputs, bytearray.compare)
    let cond0 =
      actual == expected && policies(vMint) == [encoinsSymb]
    
    let cond0msgs = fromCondMsgs(
        [ @"cond0:"
        , @"actual: ", cbor.diagnostic(actual)
        , @"expected: ", cbor.diagnostic(expected)
        , @"policies: ", cbor.diagnostic(policies(vMint))
        ])

    // Condition 1
    let cond1 =
      verify_ed25519_signature(verifierPKH, hashRedeemer(red), sig)
    // Condition 2
    let refIns =
      map(info.reference_inputs, fn(x) { x.output })
    let cond2 =
      any(
        refIns,
        fn(o) {
          o.address == ledgerAddr && isNonnegativeValue(
            merge(o.value, negate(beacon)),
          )
        },
      )
    let cond2msgs = fromCondMsgs(
        [ @"cond2:"
        , @"refIns:", cbor.diagnostic(refIns)
        ])

    // Conditions 3 and 4
    let ins =
      map(info.inputs, fn(x) { x.output })
    let ledgerSpentOuts =
      filter(
        ins,
        fn(x) {
          x.address == ledgerAddr && isNonnegativeValue(
            add(x.value, ada_policy_id, ada_asset_name, -(lovelace_of(minTxOutValueInLedger))),
          )
        },
      )
    // vOuts are the values flowing out of the Ledger address
    let vOuts =
      map(ledgerSpentOuts, fn(x) { x.value })
    let vOut =
      foldr(vOuts, zero(), merge)

    let ledgerProducedOuts =
      filter(
        info.outputs,
        fn(x) {
          x.address == ledgerAddr && isNonnegativeValue(
            merge(x.value, negate(minTxOutValueInLedger)),
          ) && x.datum == InlineDatum(Void)
        },
      )
    // vIns are the values flowing into the Ledger address
    let vIns =
      map(ledgerProducedOuts, fn(x) { x.value })
    let vIn =
      foldr(vIns, zero(), merge)

    // Wallet Mode
    let cond3 =
      vIn == merge(vOut, val)
    let cond3msgs = fromCondMsgs(
        [ @"cond3:"
        , @"vIn", cbor.diagnostic(vIn)
        , @"vOutWithVal", cbor.diagnostic(merge(vOut, val))
        ])

    // Ledger Mode
    let cond4 =
      vIn == merge(vOut, merge(vMint, merge(val, valDeposits)))
    let cond4msgs = fromCondMsgs(
        [ @"cond4:"
        , @"vIn = ", cbor.diagnostic(vIn)
        , @"merge(vOut, merge(vMint, merge(val, valDeposits))) = ", cbor.diagnostic(merge(vMint, merge(val, valDeposits)))
        ])

    let cond5 =
      checkLedgerOuputValue1(vIns)

    // Condition 6
    let depositsOrZero =
      if cond5 {
        deposits
      } else {
        0
      }
    let valDepositsOrZero =
      from_lovelace(depositsOrZero * 1000000)
    let cond6 =
      v + fees + depositsOrZero >= 0 || any(
        info.outputs,
        fn(o) {
          o.address == changeAddr && isNonnegativeValue(
            merge(o.value, merge(val, merge(valFees, valDepositsOrZero))),
          )
        },
      )

    // Imposing validation conditions
    
    traceOnFalse(cond0msgs, cond0) 
        && traceOnFalse(@"cond1:", cond1) 
        && traceOnFalse(cond2msgs, cond2) 
        && traceOnFalse(cond3msgs, cond3) 
        && traceOnFalse(cond4msgs, cond4 || cond5) 
        && traceOnFalse(@"cond6:", cond6) 
  }
}

validator(par: EncoinsPolicyParams) {
  fn encoinsPolicyCheck(
    red: EncoinsRedeemerOnChain,
    context: ScriptContext,
  ) -> Bool {
    // Destructuring arguments
    let info =
      context.transaction
    let vMint =
      from_minted_value(info.mint)
    expect Mint(encoinsSymb) =
      context.purpose
    let (beacon, verifierPKH) =
      par
    let ((ledgerAddr, changeAddr, feesWithSign), (v, inputs), _, sig) =
      red
    let fees =
      abs(feesWithSign)
    let val =
      from_lovelace(v * 1000000)
    let valFees =
      from_lovelace(fees * 1000000)
    let deposits =
      depositMultiplier * foldr(map(inputs, snd_pair), 0, add_integer)
    let valDeposits =
      from_lovelace(deposits * 1000000)
    let minTxOutValueInLedger =
      from_lovelace(minAdaTxOutInLedger)

    // Defining conditions
    // Condition 0
    let actual =
      tokens(vMint, encoinsSymb)
    let expected =
      from_list(inputs, bytearray.compare)
    let cond0 =
      actual == expected && policies(vMint) == [encoinsSymb]

    // Condition 1
    let cond1 =
      verify_ed25519_signature(verifierPKH, hashRedeemer(red), sig)
    // Condition 2
    let refIns =
      map(info.reference_inputs, fn(x) { x.output })
    let cond2 =
      any(
        refIns,
        fn(o) {
          o.address == ledgerAddr && isNonnegativeValue(
            merge(o.value, negate(beacon)),
          )
        },
      )

    // Conditions 3 and 4
    let ins =
      map(info.inputs, fn(x) { x.output })
    let ledgerSpentOuts =
      filter(
        ins,
        fn(x) {
          x.address == ledgerAddr && isNonnegativeValue(
            add(x.value, ada_policy_id, ada_asset_name, -(lovelace_of(minTxOutValueInLedger))),
          )
        },
      )
    // vOuts are the values flowing out of the Ledger address
    let vOuts =
      map(ledgerSpentOuts, fn(x) { x.value })
    let vOut =
      foldr(vOuts, zero(), merge)

    let ledgerProducedOuts =
      filter(
        info.outputs,
        fn(x) {
          x.address == ledgerAddr && isNonnegativeValue(
            merge(x.value, negate(minTxOutValueInLedger)),
          ) && x.datum == InlineDatum(Void)
        },
      )
    // vIns are the values flowing into the Ledger address
    let vIns =
      map(ledgerProducedOuts, fn(x) { x.value })
    let vIn =
      foldr(vIns, zero(), merge)

    // Wallet Mode
    let cond3 =
      vIn == merge(vOut, val)

    // Ledger Mode
    let cond4 =
      vIn == merge(vOut, merge(vMint, merge(val, valDeposits)))

    let cond5 =
      checkLedgerOuputValue1(vIns)

    // Condition 6
    let depositsOrZero =
      if cond5 {
        deposits
      } else {
        0
      }
    let valDepositsOrZero =
      from_lovelace(depositsOrZero * 1000000)
    let cond6 =
      v + fees + depositsOrZero >= 0 || any(
        info.outputs,
        fn(o) {
          o.address == changeAddr && isNonnegativeValue(
            merge(o.value, merge(val, merge(valFees, valDepositsOrZero))),
          )
        },
      )

    // Imposing validation conditions
    cond0 && cond1 && cond2 && cond3 && ( cond4 || cond5 ) && cond6
  }
}

type EncoinsLedgerValidatorParams {
  policyId: PolicyId,
}

validator(encoinsSymb: EncoinsLedgerValidatorParams) {
  fn ledgerValidatorCheck(
    _datum: Void,
    _redeemer: Void,
    context: ScriptContext,
  ) -> Bool {
    let policyId =
      encoinsSymb.policyId
    let info =
      context.transaction
    let rdmrs =
      info.redeemers
    let purp =
      Mint(policyId)
    has_key(rdmrs, purp)
  }
}

validator(par: Int) {
  fn scriptLoadTest(
    _datum: Void,
    redeemer: Int,
    _context: ScriptContext,
  ) -> Bool {
    redeemer == par
  }
}
