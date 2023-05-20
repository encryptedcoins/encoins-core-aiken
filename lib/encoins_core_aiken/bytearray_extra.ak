use aiken/builtin.{append_bytearray, cons_bytearray}
use aiken/transaction/credential.{
  Address, Inline, ScriptCredential, VerificationKeyCredential,
}

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

pub fn addressToBytes(a: Address) -> ByteArray {
  let paymentPart =
    when a.payment_credential is {
      VerificationKeyCredential(cred) ->
        cred
      ScriptCredential(cred) ->
        cred
    }
  let stakingPart =
    when a.stake_credential is {
      Some(Inline(s)) ->
        when s is {
          VerificationKeyCredential(cred) ->
            cred
          ScriptCredential(cred) ->
            cred
        }
      _ ->
        #""
    }
  append_bytearray(paymentPart, stakingPart)
}
