# proofs of laws/FixedWritesValidNumbers.bend
import Base
import ../src/value.bend as V
import ../src/fixed.bend as F
import ../laws/FixedWritesValidNumbers.bend as Laws

def Laws.fixed_none(txt, nn, h):
  %Equal.sym(Bool, V.num.ok(txt), False{}, h)
    : {F.fixed.go(_, txt, nn) == None{} : Maybe<&2, String>}
  {==}

def Laws.fixed_some(txt, nn, h):
  %Equal.sym(Bool, V.num.ok(txt), True{}, h)
    : {F.fixed.go(_, txt, nn) == Some{F.text(txt, nn)} : Maybe<&2, String>}
  {==}
