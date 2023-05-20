// Originally defined in ENCOINS.BaseTypes
pub type MintingPolarity {
  MintCoin
  BurnCoin
}

pub fn polarityToInteger(p: MintingPolarity) -> Int {
  if p == MintCoin {
    1
  } else {
    -1
  }
}

pub fn polarityToInteger2(p: MintingPolarity) -> Int {
  if p == BurnCoin {
    -1
  } else {
    1
  }
}

pub fn inputToEncoinsWithPolarity(a: (ByteArray, MintingPolarity)) -> (ByteArray, Int) {
  let (bs, p) = a
  (bs, polarityToInteger(p))
}