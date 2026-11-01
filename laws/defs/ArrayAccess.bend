# whether a value is an array, and a list's value at a position
import Base
import ../../src/value.bend as V

# an array
def is_arr(val: V.Json) -> Bool:
  match val:
    case V.JArr{_}:
      True{}
    case _:
      False{}

# the list's value at a position; null past the end
def nth(+xs: List<&2, V.Json>, left: Nat) -> V.Json:
  match xs:
    case Nil{}:
      V.JNull{}
    case hd <> tl:
      match left:
        case 0n:
          hd
        case 1n+pp:
          nth(tl, pp)
