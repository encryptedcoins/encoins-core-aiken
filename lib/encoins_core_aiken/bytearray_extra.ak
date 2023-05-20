use aiken/builtin.{cons_bytearray}

// use aiken/transaction/credential.{Address, payment_credential}

pub fn integerToBytes(n: Int) -> ByteArray {
  let q =
    n / 256
  let r =
    n % 256
  cons_bytearray(
    r,
    if q > 0 {
      integerToBytes(q)
    } else {
      #""
    },
  )
}
// pub fn addressToBytes(a: Address) -> ByteArray {
//   let paymentPart =
//     when payment_credential(a) is {
//       VerificationKeyCredential(cred) ->
//         cred
//       ScriptCredential(cred) ->
//         cred
//     }
//   let stakingPart =
//     when staking_credential(a) is {
//       Some(Inline(s)) ->
//         when s is {
//           VerificationKeyCredential(cred) ->
//             cred
//           ScriptCredential(cred) ->
//             cred
//         }
//       _ ->
//         #""
//     }
// }
