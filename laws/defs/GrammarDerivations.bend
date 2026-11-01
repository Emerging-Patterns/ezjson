# RFC 8259's value rule as derivations, and string pieces with their escapes
import Base
import ../../src/fixed.bend as F
import ./CursorAndNumberRules.bend as D1

# the character a two-character escape stands for, RFC 8259 §7: \" \\ \/
# \b \f \n \r \t; none for any other character after a backslash
def unesc(+ch: Char) -> Maybe<&2, Char>:
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 34), Some{'"'},
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 92), Some{'\\'},
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 47), Some{'/'},
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 98), Some{Char.from_u32(8)},
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 102), Some{Char.from_u32(12)},
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 110), Some{'\n'},
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 114), Some{'\r'},
  Bool.pick(Maybe<&2, Char>, D1.is_cp(ch, 116), Some{'\t'},
    None{}))))))))

# a hexadecimal digit: 0 to 9, A to F, a to f (§7)
def hexd(+ch: Char) -> Bool:
  Bool.or(Bool.and(U32.is_ge(Char.to_u32(ch), 48), U32.is_le(Char.to_u32(ch), 57)),
    Bool.or(Bool.and(U32.is_ge(Char.to_u32(ch), 65), U32.is_le(Char.to_u32(ch), 70)),
      Bool.and(U32.is_ge(Char.to_u32(ch), 97), U32.is_le(Char.to_u32(ch), 102))))

# a hexadecimal digit's value
def hexv(+ch: Char) -> U32:
  +x = Char.to_u32(ch)
  Bool.pick(U32, U32.is_le(x, 57), (x - 48 : U32), Bool.pick(U32, U32.is_ge(x, 97), (x - 87 : U32), (x - 55 : U32)))

# one more hexadecimal digit, in base 16
def hex.acc(acc: U32, +ch: Char) -> U32:
  (acc * 16 + hexv(ch) : U32)

# the code point four hexadecimal digits spell
def hex4(+aa: Char, +bb: Char, +cc: Char, +dd: Char) -> U32:
  hex.acc(hex.acc(hex.acc(hex.acc(0, aa), bb), cc), dd)

# a high surrogate, D800 to DBFF
def in_hi(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 55296), U32.is_le(cp, 56319))

# D800 to DFFF's upper half, DC00 to DFFF
def in_lo(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 56320), U32.is_le(cp, 57343))

# a low surrogate: in DC00 to DFFF, and so not a high one
def lo_sur(+cp: U32) -> Bool:
  Bool.and(Bool.not(in_hi(cp)), in_lo(cp))

# a code point that is no surrogate
def non_sur(+cp: U32) -> Bool:
  Bool.and(Bool.not(in_hi(cp)), Bool.not(in_lo(cp)))

# the character a Maybe holds, or dflt
def some_or(mb: Maybe<&2, Char>, dflt: Char) -> Char:
  match mb:
    case None{}:
      dflt
    case Some{ch}:
      ch

# whether a Maybe holds a character
def has_char(mb: Maybe<&2, Char>) -> Bool:
  match mb:
    case None{}:
      False{}
    case Some{_}:
      True{}

# one piece of a string's spelling between its quotation marks (§7): a raw
# character, a two-character escape, a \u escape, or a high and a low
# surrogate's \u escapes
type Piece is Data:
  PRaw{ch: Char}
  PEsc{ch: Char}
  PU{aa: Char, bb: Char, cc: Char, dd: Char}
  PPair{h1: Char, h2: Char, h3: Char, h4: Char, l1: Char, l2: Char, l3: Char, l4: Char}

# how a piece is written
def piece.text(pc: Piece) -> String:
  match pc:
    case PRaw{ch}:
      SCon{ch, ""}
    case PEsc{ch}:
      SCon{'\\', SCon{ch, ""}}
    case PU{aa, bb, cc, dd}:
      SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, ""}}}}}}
    case PPair{h1, h2, h3, h4, l1, l2, l3, l4}:
      SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3,
        SCon{l4, ""}}}}}}}}}}}}

# whether a piece is well spelled: a raw character a string keeps, one of the
# two-character escapes, four hex digits of a code point that is no
# surrogate, or four of a high surrogate and then four of a low one
def piece.ok(pc: Piece) -> Bool:
  match pc:
    case PRaw{+ch}:
      D1.raw_char(ch)
    case PEsc{+ch}:
      has_char(unesc(ch))
    case PU{+aa, +bb, +cc, +dd}:
      Bool.and(Bool.and(hexd(aa), Bool.and(hexd(bb), Bool.and(hexd(cc), hexd(dd)))), non_sur(hex4(aa, bb, cc, dd)))
    case PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      Bool.and(Bool.and(hexd(h1), Bool.and(hexd(h2), Bool.and(hexd(h3), hexd(h4)))),
        Bool.and(Bool.and(hexd(l1), Bool.and(hexd(l2), Bool.and(hexd(l3), hexd(l4)))),
          Bool.and(in_hi(hex4(h1, h2, h3, h4)), lo_sur(hex4(l1, l2, l3, l4)))))

# the character a piece stands for
def piece.char(pc: Piece) -> Char:
  match pc:
    case PRaw{ch}:
      ch
    case PEsc{+ch}:
      some_or(unesc(ch), ch)
    case PU{+aa, +bb, +cc, +dd}:
      Char.from_u32(hex4(aa, bb, cc, dd))
    case PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      Char.from_u32(D1.pair(hex4(h1, h2, h3, h4), hex4(l1, l2, l3, l4)))

# how pieces are written, one after another
def spell(ps: List<&2, Piece>) -> String:
  match ps:
    case Nil{}:
      ""
    case pc <> tl:
      piece.text(pc) ++ spell(tl)

# the characters pieces stand for
def spelled(ps: List<&2, Piece>) -> String:
  match ps:
    case Nil{}:
      ""
    case pc <> tl:
      SCon{piece.char(pc), spelled(tl)}

# whether every piece is well spelled
def spell_ok(ps: List<&2, Piece>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case pc <> tl:
      Bool.and(piece.ok(pc), spell_ok(tl))

# a derivation of RFC 8259's value rule (§3 to §7), whitespace included: a
# literal name or a number (§3, §6), a string of pieces (§7), an empty array
# or object, or one with its first element or member (§4, §5), and the cells
# after it: the end, then a comma and the next element or member. The
# whitespace fields sit where §2 allows whitespace: after `[` and `{`, around
# `:` and `,`, and before `]` and `}`
type Gv is Data:
  GWord{w: String}
  GStr{ps: List<&2, Piece>}
  GArr0{w0: String}
  GArr{w0: String, vv: Gv, w1: String, rr: Gv}
  GObj0{w0: String}
  GObj{w0: String, ps: List<&2, Piece>, w1: String, w2: String, vv: Gv, w3: String, rr: Gv}
  GEnd{}
  GNext{w2: String, vv: Gv, w1: String, rr: Gv}
  GNextM{w4: String, ps: List<&2, Piece>, w1: String, w2: String, vv: Gv, w3: String, rr: Gv}

# where a derivation stands: a value, an array's cells after an element, or
# an object's cells after a member
type GK is Data:
  GKVal{}
  GKArr{}
  GKObj{}

# the text a derivation spells
def g.text(gg: Gv) -> String:
  match gg:
    case GWord{w}:
      w
    case GStr{ps}:
      "\"" ++ spell(ps) ++ "\""
    case GArr0{w0}:
      "[" ++ w0 ++ "]"
    case GArr{w0, vv, w1, rr}:
      "[" ++ w0 ++ g.text(vv) ++ w1 ++ g.text(rr) ++ "]"
    case GObj0{w0}:
      "{" ++ w0 ++ "}"
    case GObj{w0, ps, w1, w2, vv, w3, rr}:
      "{" ++ w0 ++ "\"" ++ spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ g.text(vv) ++ w3 ++ g.text(rr) ++ "}"
    case GEnd{}:
      ""
    case GNext{w2, vv, w1, rr}:
      "," ++ w2 ++ g.text(vv) ++ w1 ++ g.text(rr)
    case GNextM{w4, ps, w1, w2, vv, w3, rr}:
      "," ++ w4 ++ "\"" ++ spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ g.text(vv) ++ w3 ++ g.text(rr)

# whether a derivation follows the rules where it stands: words are literal
# names or numbers, strings are well spelled, whitespace is whitespace, and
# each cell is one that may stand there
def g.ok(gg: Gv, kk: GK) -> Bool:
  match gg kk:
    case GWord{+w} GKVal{}:
      D1.lit_or_num(w)
    case GStr{ps} GKVal{}:
      spell_ok(ps)
    case GArr0{+w0} GKVal{}:
      D1.all_ws(w0)
    case GArr{+w0, vv, +w1, rr} GKVal{}:
      Bool.and(D1.all_ws(w0), Bool.and(g.ok(vv, GKVal{}), Bool.and(D1.all_ws(w1), g.ok(rr, GKArr{}))))
    case GObj0{+w0} GKVal{}:
      D1.all_ws(w0)
    case GObj{+w0, ps, +w1, +w2, vv, +w3, rr} GKVal{}:
      Bool.and(D1.all_ws(w0), Bool.and(spell_ok(ps), Bool.and(D1.all_ws(w1), Bool.and(D1.all_ws(w2), Bool.and(g.ok(vv,
        GKVal{}), Bool.and(D1.all_ws(w3), g.ok(rr, GKObj{})))))))
    case GEnd{} GKArr{}:
      True{}
    case GNext{+w2, vv, +w1, rr} GKArr{}:
      Bool.and(D1.all_ws(w2), Bool.and(g.ok(vv, GKVal{}), Bool.and(D1.all_ws(w1), g.ok(rr, GKArr{}))))
    case GEnd{} GKObj{}:
      True{}
    case GNextM{+w4, ps, +w1, +w2, vv, +w3, rr} GKObj{}:
      Bool.and(D1.all_ws(w4), Bool.and(spell_ok(ps), Bool.and(D1.all_ws(w1), Bool.and(D1.all_ws(w2), Bool.and(g.ok(vv,
        GKVal{}), Bool.and(D1.all_ws(w3), g.ok(rr, GKObj{})))))))
    case _ _:
      False{}

# whether whitespace, a derivation and whitespace are RFC 8259's JSON-text
# rule (§2): ws value ws
def derived(+wa: String, gg: Gv, +wb: String) -> Bool:
  Bool.and(D1.all_ws(wa), Bool.and(g.ok(gg, GKVal{}), D1.all_ws(wb)))
