# `quote(s)` escapes exactly `"`, `\` and U+0000 to U+001F, using the
# two-character form where one exists and `\u00xx` otherwise, and writes every
# other scalar value as itself, and writes U+FFFD for every code point that is
# not a Unicode scalar value (a surrogate, or past U+10FFFF) (§7, §8.1)
import Base
import ../src/print.bend as Print
import ./defs/CursorAndNumberRules.bend as D1

# the lowercase hexadecimal digits, in order
def hex_lower() -> String:
  "0123456789abcdef"

# the character at a position of a text; U+0000 past its end
def char_at(+txt: String, left: Nat) -> Char:
  match txt left:
    case SNil{} _:
      Char.from_u32(0)
    case SCon{hd, _} 0n:
      hd
    case SCon{_, tl} 1n+pp:
      char_at(tl, pp)

# LAW: print writes a code point that is not a Unicode scalar value as U+FFFD
law print_non_scalar:
  for +ch: Char
  for h_non: {D1.non_scalar(Char.to_u32(ch)) == True{} : Bool}
  {Print.escape.char(ch) == String.from_list([Char.from_u32(65533)]) : String}

# LAW: print escapes a quotation mark as backslash, quotation mark
law esc_quote:
  for +ch: Char
  for h_eq: {ch == '"' : Char}
  {Print.escape.char(ch) == "\\\"" : String}

# LAW: print escapes a reverse solidus as two
law esc_backslash:
  for +ch: Char
  for h_eq: {ch == '\\' : Char}
  {Print.escape.char(ch) == "\\\\" : String}

# LAW: print writes a backspace as its two-character escape
law esc_b:
  for +ch: Char
  for h_eq: {ch == '\u{8}' : Char}
  {Print.escape.char(ch) == "\\b" : String}

# LAW: print writes a form feed as its two-character escape
law esc_f:
  for +ch: Char
  for h_eq: {ch == '\u{c}' : Char}
  {Print.escape.char(ch) == "\\f" : String}

# LAW: print writes a line feed as its two-character escape
law esc_n:
  for +ch: Char
  for h_eq: {ch == '\n' : Char}
  {Print.escape.char(ch) == "\\n" : String}

# LAW: print writes a carriage return as its two-character escape
law esc_r:
  for +ch: Char
  for h_eq: {ch == '\r' : Char}
  {Print.escape.char(ch) == "\\r" : String}

# LAW: print writes a tab as its two-character escape
law esc_t:
  for +ch: Char
  for h_eq: {ch == '\t' : Char}
  {Print.escape.char(ch) == "\\t" : String}

# LAW: print writes every other scalar value at or above U+0020 as itself
law esc_plain:
  for +ch: Char
  for h_scalar: {D1.non_scalar(Char.to_u32(ch)) == False{} : Bool}
  for +h_ctl: {U32.is_lt(Char.to_u32(ch), 32) == False{} : Bool}
  for h_quote: {ch != '"' : Char}
  for h_back: {ch != '\\' : Char}
  {Print.escape.char(ch) == String.from_list([ch]) : String}

# LAW: print writes every other control below U+0020 as \u00 and two
# lowercase hex digits
law esc_ctl:
  for +ch: Char
  for h_ctl: {U32.is_lt(Char.to_u32(ch), 32) == True{} : Bool}
  for h_b: {ch != '\u{8}' : Char}
  for h_f: {ch != '\u{c}' : Char}
  for h_n: {ch != '\n' : Char}
  for h_r: {ch != '\r' : Char}
  for h_t: {ch != '\t' : Char}
  {Print.escape.char(ch) == "\\u00" ++ String.from_list([char_at(hex_lower(), U32.to_nat(U32.div(Char.to_u32(ch), 16))),
    char_at(hex_lower(), U32.to_nat(U32.mod(Char.to_u32(ch), 16)))]) : String}
