# proofs of laws/QuoteEscapesExactly.bend
import Base
import ../src/print.bend as Print
import ../laws/QuoteEscapesExactly.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/LexemeOrder.bend as M2
import ./lemmas/WellFormedCells.bend as M3

def Laws.print_non_scalar(ch, h_non):
  ok = Equal.sym(Bool, D1.non_scalar(Char.to_u32(ch)), True{}, h_non)
  %ok : {Print.escape.scalar(Char.to_u32(ch), ch, Bool.not(_))
    == String.from_list([Char.from_u32(65533)]) : String}
  {==}

# a U32 that is not k compares unequal to it, once the answer is named
law neq_at:
  for +cp: U32
  for +kk: U32
  for bb: Bool
  for eb: {U32.is_eq(cp, kk) == bb : Bool}
  for contra: {cp == kk : U32} -> Empty
  {U32.is_eq(cp, kk) == False{} : Bool}

def neq_at(cp, kk, bb, eb, contra):
  match bb:
    case False{}:
      eb
    case True{}:
      Empty.absurd({U32.is_eq(cp, kk) == False{} : Bool}, contra(M3.ueq(cp, kk, eb)))

# a code point of U+0020 or more is none of the controls
law ctl_clash:
  for +uu: U32
  for kk: U32
  for h_kk: {U32.is_lt(kk, 32) == True{} : Bool}
  for h_ctl: {U32.is_lt(uu, 32) == False{} : Bool}
  for ee: {uu == kk : U32}
  Empty

def ctl_clash(uu, kk, h_kk, h_ctl, ee):
  lt = Equal.cong(U32, Bool, xx => U32.is_lt(xx, 32), uu, kk, ee)
  M1.true_false(Equal.trans(Bool, True{}, U32.is_lt(uu, 32), False{},
    Equal.trans(Bool, True{}, U32.is_lt(kk, 32), U32.is_lt(uu, 32), Equal.sym(Bool, U32.is_lt(kk, 32), True{}, h_kk),
      Equal.sym(Bool, U32.is_lt(uu, 32), U32.is_lt(kk, 32), lt)), h_ctl))

# a character that differs from Chr{kk} has a different code
law chr_clash:
  for +uu: U32
  for kk: U32
  for h_ne: {Chr{uu} != Chr{kk} : Char}
  for ee: {uu == kk : U32}
  Empty

def chr_clash(uu, kk, h_ne, ee):
  h_ne(Equal.cong(U32, Char, xx => Chr{xx}, uu, kk, ee))

def Laws.esc_quote(ch, h_eq):
  ec = Equal.sym(Char, ch, '"', h_eq)
  %ec : {Print.escape.char(_) == "\\\"" : String}
  {==}

def Laws.esc_backslash(ch, h_eq):
  ec = Equal.sym(Char, ch, '\\', h_eq)
  %ec : {Print.escape.char(_) == "\\\\" : String}
  {==}

def Laws.esc_b(ch, h_eq):
  ec = Equal.sym(Char, ch, '\u{8}', h_eq)
  %ec : {Print.escape.char(_) == "\\b" : String}
  {==}

def Laws.esc_f(ch, h_eq):
  ec = Equal.sym(Char, ch, '\u{c}', h_eq)
  %ec : {Print.escape.char(_) == "\\f" : String}
  {==}

def Laws.esc_n(ch, h_eq):
  ec = Equal.sym(Char, ch, '\n', h_eq)
  %ec : {Print.escape.char(_) == "\\n" : String}
  {==}

def Laws.esc_r(ch, h_eq):
  ec = Equal.sym(Char, ch, '\r', h_eq)
  %ec : {Print.escape.char(_) == "\\r" : String}
  {==}

def Laws.esc_t(ch, h_eq):
  ec = Equal.sym(Char, ch, '\t', h_eq)
  %ec : {Print.escape.char(_) == "\\t" : String}
  {==}

def Laws.esc_plain(ch, h_scalar, h_ctl, h_quote, h_back):
  match ch:
    case Chr{+u}:
      sc = Equal.sym(Bool, D1.non_scalar(u), False{}, h_scalar)
      %sc : {Print.escape.scalar(u, Chr{u}, Bool.not(_)) == String.from_list([Chr{u}]) : String}
      n34 = Equal.sym(Bool, U32.is_eq(u, 34), False{},
        neq_at(u, 34, U32.is_eq(u, 34), {==}, cc => chr_clash(u, 34, h_quote, cc)))
      %n34 : {Bool.pick(String, _, "\\\"",
        Bool.pick(String, U32.is_eq(u, 92), "\\\\",
          Bool.pick(String, U32.is_eq(u, 8), "\\b",
            Bool.pick(String, U32.is_eq(u, 12), "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n92 = Equal.sym(Bool, U32.is_eq(u, 92), False{},
        neq_at(u, 92, U32.is_eq(u, 92), {==}, cc => chr_clash(u, 92, h_back, cc)))
      %n92 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, _, "\\\\",
          Bool.pick(String, U32.is_eq(u, 8), "\\b",
            Bool.pick(String, U32.is_eq(u, 12), "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n8 = Equal.sym(Bool, U32.is_eq(u, 8), False{},
        neq_at(u, 8, U32.is_eq(u, 8), {==}, cc => ctl_clash(u, 8, {==}, h_ctl, cc)))
      %n8 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, _, "\\b",
            Bool.pick(String, U32.is_eq(u, 12), "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n12 = Equal.sym(Bool, U32.is_eq(u, 12), False{},
        neq_at(u, 12, U32.is_eq(u, 12), {==}, cc => ctl_clash(u, 12, {==}, h_ctl, cc)))
      %n12 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, _, "\\f",
              Bool.pick(String, U32.is_eq(u, 10), "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n10 = Equal.sym(Bool, U32.is_eq(u, 10), False{},
        neq_at(u, 10, U32.is_eq(u, 10), {==}, cc => ctl_clash(u, 10, {==}, h_ctl, cc)))
      %n10 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, False{}, "\\f",
              Bool.pick(String, _, "\\n",
                Bool.pick(String, U32.is_eq(u, 13), "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n13 = Equal.sym(Bool, U32.is_eq(u, 13), False{},
        neq_at(u, 13, U32.is_eq(u, 13), {==}, cc => ctl_clash(u, 13, {==}, h_ctl, cc)))
      %n13 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, False{}, "\\f",
              Bool.pick(String, False{}, "\\n",
                Bool.pick(String, _, "\\r",
                  Bool.pick(String, U32.is_eq(u, 9), "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      n9 = Equal.sym(Bool, U32.is_eq(u, 9), False{},
        neq_at(u, 9, U32.is_eq(u, 9), {==}, cc => ctl_clash(u, 9, {==}, h_ctl, cc)))
      %n9 : {Bool.pick(String, False{}, "\\\"",
        Bool.pick(String, False{}, "\\\\",
          Bool.pick(String, False{}, "\\b",
            Bool.pick(String, False{}, "\\f",
              Bool.pick(String, False{}, "\\n",
                Bool.pick(String, False{}, "\\r",
                  Bool.pick(String, _, "\\t", Print.escape.rest(u, Chr{u}))))))))
        == String.from_list([Chr{u}]) : String}
      ct = Equal.sym(Bool, U32.is_lt(u, 32), False{}, h_ctl)
      %ct : {Print.escape.rest.go(u, Chr{u}, _) == String.from_list([Chr{u}]) : String}
      {==}

# what esc_ctl says of a control, its other hypotheses first
def esc_eq(uu: U32) -> Type:
  {Print.escape.char(Chr{uu}) == "\\u00" ++ String.from_list([Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.div(uu,
    16))),
    Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.mod(uu, 16)))]) : String}

def esc_goal(uu: U32) -> Type:
  {Chr{uu} != '\u{8}' : Char} -> {Chr{uu} != '\u{c}' : Char} -> {Chr{uu} != '\n' : Char} ->
    {Chr{uu} != '\r' : Char} -> {Chr{uu} != '\t' : Char} -> esc_eq(uu)

# esc_ctl, one control at a time
law esc_ctl5:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, M3.zw(26n)}}}}}}})

def esc_ctl5(b0, b1, b2, b3, b4):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} False{} True{} False{}:
      h_b => _h_f => _h_n => _h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{False{}, WCon{False{}, WCon{False{},
        WCon{True{}, WCon{False{}, WCon{False{}, M3.zw(26n)}}}}}}}), h_b({==}))
    case False{} False{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} False{} True{} True{} False{}:
      _h_b => h_f => _h_n => _h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{False{}, WCon{False{}, WCon{True{},
        WCon{True{}, WCon{False{}, WCon{False{}, M3.zw(26n)}}}}}}}), h_f({==}))
    case False{} False{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} False{} True{} False{}:
      _h_b => _h_f => h_n => _h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{False{}, WCon{True{}, WCon{False{},
        WCon{True{}, WCon{False{}, WCon{False{}, M3.zw(26n)}}}}}}}), h_n({==}))
    case False{} True{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case False{} True{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} False{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => h_t => Empty.absurd(esc_eq(U32{WCon{True{}, WCon{False{}, WCon{False{},
        WCon{True{}, WCon{False{}, WCon{False{}, M3.zw(26n)}}}}}}}), h_t({==}))
    case True{} False{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} False{} True{} True{} False{}:
      _h_b => _h_f => _h_n => h_r => _h_t => Empty.absurd(esc_eq(U32{WCon{True{}, WCon{False{}, WCon{True{},
        WCon{True{}, WCon{False{}, WCon{False{}, M3.zw(26n)}}}}}}}), h_r({==}))
    case True{} False{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} False{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} False{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} False{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} True{} False{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}
    case True{} True{} True{} True{} True{}:
      _h_b => _h_f => _h_n => _h_r => _h_t => {==}

# esc_ctl, once bit 5 and the bits above are known
law esc_ctl.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, M3.zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}})

def esc_ctl.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, M3.zw(26n)), LT{}, ec)
      Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
        M1.true_false(Equal.trans(Bool, True{},
        Cmp.is_lt(Word.cmp(26n, rest, M3.zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, M3.zw(26n))), True{}, ez), M3.zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, rest}}}}}}}),
            M2.false_true(h_lt))
        case True{}:
          Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            M2.false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            M2.false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, M3.zw(26n),
            M3.weq(26n, rest, M3.zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, M3.zw(26n)),
                EQ{}, ec)))
          %er : esc_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}})
          esc_ctl5(b0, b1, b2, b3, b4)

# a control below U+0020, other than the five with two-character escapes
law esc_ctl.go:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  esc_goal(uu)

def esc_ctl.go(uu, h_lt):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, M3.zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = M3.lt_up(b4, c5, M3.lt_up(b3, c4, M3.lt_up(b2, c3, M3.lt_up(b1, c2, M3.lt_up(b0, c1, h_lt)))))
      esc_ctl.at(Word.cmp(26n, rest, M3.zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5)

def Laws.esc_ctl(ch, h_ctl, h_b, h_f, h_n, h_r, h_t):
  match ch:
    case Chr{+uu}:
      esc_ctl.go(uu, h_ctl)(h_b, h_f, h_n, h_r, h_t)
