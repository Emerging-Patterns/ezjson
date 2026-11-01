# num.ok's states against the number grammar
import Base
import ../../src/value.bend as V

# RFC 8259 §6: num.ok's states against the grammar. One lemma per state,
# from the last state back to the start; each `_at` lemma takes the answer
# of one character test as a parameter, so it can match on it

# a rejected number stays rejected
law st_bad:
  for +cs: List<&2, Char>
  {V.num.ok.go(cs, V.NBad{}) == False{} : Bool}

def st_bad(cs):
  match cs:
    case Nil{}:
      {==}
    case _ch <> tl:
      st_bad(tl)
