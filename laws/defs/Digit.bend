# the ABNF DIGIT rule
import Base

# DIGIT = %x30-39
def digit(+ch: Char) -> Bool:
  Bool.and(U32.is_ge(Char.to_u32(ch), 48), U32.is_le(Char.to_u32(ch), 57))
