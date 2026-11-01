# whether a value is an object
import Base
import ../../src/value.bend as V

# an object
def is_obj(val: V.Json) -> Bool:
  match val:
    case V.JObj{_}:
      True{}
    case _:
      False{}
