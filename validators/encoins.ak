use aiken/builtin.{serialise_data, verify_ed25519_signature}
use aiken/bytearray
use aiken/dict.{from_list, has_key}
use aiken/hash.{sha2_256}
use aiken/int
use aiken/list.{
  all, any, difference, filter, foldr, head, length, map, sort, tail,
}
use aiken/option.{or_else}
use aiken/transaction.{InlineDatum, Mint, ScriptContext}
use aiken/transaction/credential.{Address}
use aiken/transaction/value.{
  PolicyId, Value, add, flatten, from_lovelace, lovelace_of, negate, policies,
  tokens, without_lovelace, zero,
}
use encoins_core_aiken/minting_polarity.{
  MintingPolarity, inputToEncoinsWithPolarity,
}
use encoins_core_aiken/value_extra.{isNonnegativeValue}

const minAdaTxOutInLedger =
  1500000

type EncoinsPolicyParams =
  (Value, ByteArray)

type TxParams =
  (Address, Address)

type EncoinsInput =
  (Int, List<(ByteArray, MintingPolarity)>)

type ProofHash =
  ByteArray

type ProofSignature =
  ByteArray

type EncoinsRedeemerOnChain =
  (TxParams, EncoinsInput, ProofHash, ProofSignature)

// NOTE: this is different from the Haskell version
fn hashRedeemer(red: EncoinsRedeemerOnChain) -> ByteArray {
  // let ((ledgerAddr, changeAddr), (v, inputs), proofHash, _) =
  //   red
  // sha2_256(
  //   append_bytearray(
  //     addressToBytes(ledgerAddr),
  //     append_bytearray(
  //       addressToBytes(changeAddr),
  //       append_bytearray(integerToBytes(v), append_bytearray(inputs, proofHash)),
  //     ),
  //   ),
  // )
  sha2_256(serialise_data(red))
}

validator(par: EncoinsPolicyParams) {
  fn encoinsPolicyCheck(
    red: EncoinsRedeemerOnChain,
    context: ScriptContext,
  ) -> Bool {
    // Destructuring arguments 
    let info =
      context.transaction
    let (beacon, verifierPKH) =
      par
    let ((ledgerAddr, changeAddr), (v, inputs), _, sig) =
      red
    let val =
      from_lovelace(v * 1000000)
    let vMint =
      info.mint
    expect Mint(encoinsSymb) =
      context.purpose

    // Defining conditions
    // Condition 0
    let actual =
      tokens(vMint, encoinsSymb)
    // NOTE: this is different from the Haskell version,
    // where duplicates in `inputs` will cause the transaction to fail
    let expected =
      from_list(map(inputs, inputToEncoinsWithPolarity), bytearray.compare)
    let cond0 =
      actual == expected && policies(vMint) == [encoinsSymb]

    // Condition 1
    let cond1 =
      verify_ed25519_signature(verifierPKH, hashRedeemer(red), sig)

    // Condition 2
    let ins =
      map(info.inputs, fn(x) { x.output })
    let cond2 =
      any(
        ins,
        fn(o) {
          o.address == changeAddr && isNonnegativeValue(add(o.value, val))
        },
      )

    // Condition 3
    let refIns =
      map(info.reference_inputs, fn(x) { x.output })
    let cond3 =
      any(
        refIns,
        fn(o) {
          o.address == ledgerAddr && isNonnegativeValue(
            add(o.value, negate(beacon)),
          )
        },
      )

    // Conditions 4 and 5
    let ledgerSpentOuts =
      filter(ins, fn(x) { x.address == ledgerAddr })
    let vOuts =
      map(ledgerSpentOuts, fn(x) { x.value })
    let vOut =
      foldr(vOuts, add, zero())

    let ledgerProducedOuts =
      filter(
        info.outputs,
        fn(x) { x.address == ledgerAddr && x.datum == InlineDatum(Void) },
      )
    let vIns =
      map(ledgerProducedOuts, fn(x) { x.value })
    let vIn =
      foldr(vIns, add, zero())

    let cond4 =
      vIn == add(vOut, val)
    // Wallet Mode
    let cond5 =
      vIn == add(vOut, add(vMint, val))

    // Ledger Mode
    // Condition 6
    let vInsFlat =
      map(vIns, flatten)
    let txOutSize =
      sort(map(vInsFlat, length), int.compare)
    let txOutSizeHead =
      or_else(head(txOutSize), 0)
    let txOutSizeTail =
      or_else(tail(txOutSize), [])
    let cond6 =
      all(txOutSizeTail, fn(x) { x == 6 }) && txOutSizeHead <= 6

    // Condition 7
    let adaVals =
      or_else(tail(sort(map(vIns, lovelace_of), flip(int.compare))), [])
    let cond7 =
      all(adaVals, fn(x) { x == minAdaTxOutInLedger })

    // Condition 8
    let cond8 =
      difference(policies(without_lovelace(vIn)), [encoinsSymb]) == []

    // Imposing validation conditions
    cond0 && cond1 && cond2 && cond3 && ( cond4 || cond5 ) && cond6 && cond7 && cond8
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
    let info =
      context.transaction
    let rdmrs =
      info.redeemers
    let purp =
      Mint(encoinsSymb.policyId)

    has_key(rdmrs, purp)
  }
}
