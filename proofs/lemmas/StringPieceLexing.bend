# well spelled string pieces, read by the lexer inside a string
import Base
import ../../src/lex.bend as Lex
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/GrammarDerivations.bend as D2
import ./CharacterScan.bend as M1
import ./LexemeOrder.bend as M2
import ./StringTokens.bend as M3

# laws/NamesCompareDecoded.bend: names compare decoded

# an and with True on the right
law and_t:
  for aa: Bool
  for h: {aa == True{} : Bool}
  {Bool.and(aa, True{}) == True{} : Bool}

def and_t(aa, h):
  match aa:
    case True{}:
      {==}
    case False{}:
      M2.no({Bool.and(False{}, True{}) == True{} : Bool}, h)

# a Maybe that holds a character holds the one some_or reads
law some_is:
  for mb: Maybe<&2, Char>
  for +dflt: Char
  for h: {D2.has_char(mb) == True{} : Bool}
  {mb == Some{D2.some_or(mb, dflt)} : Maybe<&2, Char>}

def some_is(mb, dflt, h):
  match mb:
    case None{}:
      M2.no({None{} == Some{D2.some_or(None{}, dflt)} : Maybe<&2, Char>}, h)
    case Some{_ch}:
      {==}

# one well spelled piece, read inside a string
law piece_lex:
  for pc: D2.Piece
  for +h: {D2.piece.ok(pc) == True{} : Bool}
  for +bf: List<&2, Char>
  {Lex.run(String.to_list(D2.piece.text(pc)), Lex.Lex{Lex.Str{}, bf, []}) == Lex.Lex{Lex.Str{},
    D2.piece.char(pc) <> bf, []} : Lex.Lex}

def piece_lex(pc, h, bf):
  match pc:
    case D2.PRaw{+ch}:
      M3.lex_raw([ch], and_t(D1.raw_char(ch), h), bf, [])
    case D2.PEsc{ch}:
      match ch:
        case Chr{+uu}:
          M1.esc_to(U32.is_eq(uu, 117), uu, D2.some_or(D2.unesc(Chr{uu}), Chr{uu}), bf, {==},
            some_is(D2.unesc(Chr{uu}), Chr{uu}, h))
    case D2.PU{+aa, +bb, +cc, +dd}:
      Equal.trans(Lex.Lex, Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, bf, []})))),
        Lex.unicode.end(D2.hex4(aa, bb, cc, dd), bf, []), Lex.Lex{Lex.Str{}, Chr{D2.hex4(aa, bb, cc, dd)} <> bf,
        []}, M1.u4_feed(aa, bb, cc, dd, bf, M1.and4_1(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd),
        M2.and_left(Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc), D2.hexd(dd)))),
        D2.non_sur(D2.hex4(aa, bb, cc, dd)), h)), M1.and4_2(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc),
        D2.hexd(dd), M2.and_left(Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc),
        D2.hexd(dd)))), D2.non_sur(D2.hex4(aa, bb, cc, dd)), h)), M1.and4_3(D2.hexd(aa), D2.hexd(bb),
        D2.hexd(cc), D2.hexd(dd), M2.and_left(Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc),
        D2.hexd(dd)))), D2.non_sur(D2.hex4(aa, bb, cc, dd)), h)), M1.and4_4(D2.hexd(aa), D2.hexd(bb),
        D2.hexd(cc), D2.hexd(dd), M2.and_left(Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc),
        D2.hexd(dd)))), D2.non_sur(D2.hex4(aa, bb, cc, dd)), h))), Equal.cong(Lex.Sur, Lex.Lex,
        zz => Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), bf, [], zz), Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)),
        Lex.SOk{}, M1.sur_ok(D2.hex4(aa, bb, cc, dd), M2.and_right(Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb),
        Bool.and(D2.hexd(cc), D2.hexd(dd)))), D2.non_sur(D2.hex4(aa, bb, cc, dd)), h))))
    case D2.PPair{+h1, +h2, +h3, +h4, +l1, +l2, +l3, +l4}:
      +hh = M2.and_left(Bool.and(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3), D2.hexd(h4)))),
        Bool.and(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
        Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)))), h)
      +r1 = M2.and_right(Bool.and(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3), D2.hexd(h4)))),
        Bool.and(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
        Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)))), h)
      +hl = M2.and_left(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
        Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4))), r1)
      +r2 = M2.and_right(Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))),
        Bool.and(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4))), r1)
      hhi = M2.and_left(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)), r2)
      hlo = M2.and_right(D2.in_hi(D2.hex4(h1, h2, h3, h4)), D2.lo_sur(D2.hex4(l1, l2, l3, l4)), r2)
      Equal.trans(Lex.Lex, Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.feed('u', Lex.feed('\\',
        Lex.feed(h4, Lex.feed(h3, Lex.feed(h2, Lex.feed(h1, Lex.Lex{Lex.Uni{3n, 0}, bf, []})))))))))), Lex.feed(l4,
        Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.feed('u', Lex.feed('\\', Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)},
        bf, []})))))), Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> bf,
        []}, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.feed('u',
        Lex.feed('\\', zz)))))), Lex.feed(h4, Lex.feed(h3, Lex.feed(h2, Lex.feed(h1, Lex.Lex{Lex.Uni{3n, 0}, bf,
        []})))), Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)}, bf, []}, Equal.trans(Lex.Lex, Lex.feed(h4, Lex.feed(h3,
        Lex.feed(h2, Lex.feed(h1, Lex.Lex{Lex.Uni{3n, 0}, bf, []})))), Lex.unicode.end(D2.hex4(h1, h2, h3, h4), bf,
        []), Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)}, bf, []}, M1.u4_feed(h1, h2, h3, h4, bf, M1.and4_1(D2.hexd(h1),
        D2.hexd(h2), D2.hexd(h3), D2.hexd(h4), hh), M1.and4_2(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3),
        D2.hexd(h4), hh), M1.and4_3(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3), D2.hexd(h4), hh),
        M1.and4_4(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3), D2.hexd(h4), hh)), Equal.cong(Lex.Sur, Lex.Lex,
        zz => Lex.unicode.end.go(D2.hex4(h1, h2, h3, h4), bf, [], zz), Lex.unicode.sur(D2.hex4(h1, h2, h3, h4)),
        Lex.SHi{}, M1.sur_hi(D2.hex4(h1, h2, h3, h4), hhi)))), Equal.trans(Lex.Lex, Lex.feed(l4, Lex.feed(l3,
        Lex.feed(l2, Lex.feed(l1, Lex.feed('u', Lex.feed('\\', Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)}, bf,
        []})))))), Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.Lex{Lex.Lo{3n, 0, D2.hex4(h1, h2, h3,
        h4)}, bf, []})))), Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3,
        l4))} <> bf, []}, {==}, Equal.trans(Lex.Lex, Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1,
        Lex.Lex{Lex.Lo{3n, 0, D2.hex4(h1, h2, h3, h4)}, bf, []})))), Lex.unicode.low.end(D2.hex4(l1, l2, l3, l4),
        D2.hex4(h1, h2, h3, h4), bf, []), Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1,
        l2, l3, l4))} <> bf, []}, M1.l4_feed(l1, l2, l3, l4, D2.hex4(h1, h2, h3, h4), bf, M1.and4_1(D2.hexd(l1),
        D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), hl), M1.and4_2(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3),
        D2.hexd(l4), hl), M1.and4_3(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), hl),
        M1.and4_4(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), hl)), Equal.cong(Lex.Sur, Lex.Lex,
        zz => Lex.unicode.low.end.go(D2.hex4(l1, l2, l3, l4), D2.hex4(h1, h2, h3, h4), bf, [], zz),
        Lex.unicode.sur(D2.hex4(l1, l2, l3, l4)), Lex.SLo{}, M1.sur_lo(D2.hex4(l1, l2, l3, l4), hlo)))))

# well spelled pieces, read inside a string
law spell_lex:
  for +ps: List<&2, D2.Piece>
  for +h: {D2.spell_ok(ps) == True{} : Bool}
  for +bf: List<&2, Char>
  {Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, bf, []}) == Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), bf), []} : Lex.Lex}

def spell_lex(ps, h, bf):
  match ps:
    case Nil{}:
      {==}
    case +pc <> +tl:
      Equal.trans(Lex.Lex, Lex.run(String.to_list(D2.piece.text(pc) ++ D2.spell(tl)), Lex.Lex{Lex.Str{}, bf, []}),
        Lex.run(String.to_list(D2.spell(tl)), Lex.Lex{Lex.Str{}, D2.piece.char(pc) <> bf, []}), Lex.Lex{Lex.Str{},
        List.reverse.go(&2, Char, String.to_list(D2.spelled(tl)), D2.piece.char(pc) <> bf), []},
        M3.seq(D2.piece.text(pc), D2.spell(tl), Lex.Lex{Lex.Str{}, bf, []}, Lex.Lex{Lex.Str{},
        D2.piece.char(pc) <> bf, []}, piece_lex(pc, M2.and_left(D2.piece.ok(pc), D2.spell_ok(tl), h), bf)),
        spell_lex(tl, M2.and_right(D2.piece.ok(pc), D2.spell_ok(tl), h), D2.piece.char(pc) <> bf))

# a token on top of a reversed prefix
law rev_snoc_t:
  for +pre: List<&2, Lex.Tok>
  for +tt: Lex.Tok
  for +acc: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, pre, [tt]), acc) == tt <> List.reverse.go(&2, Lex.Tok, pre,
    acc) : List<&2, Lex.Tok>}

def rev_snoc_t(pre, tt, acc):
  match pre:
    case Nil{}:
      {==}
    case +hd <> +tl:
      rev_snoc_t(tl, tt, hd <> acc)

# a string read back from its reversed characters
law text_k:
  for +kk: String
  {Lex.text(List.reverse.go(&2, Char, String.to_list(kk), [])) == kk : String}

def text_k(kk):
  Equal.trans(String, Lex.text(List.reverse.go(&2, Char, String.to_list(kk), [])),
    String.from_list(String.to_list(kk)) ++ "", kk, M2.text_revgo(String.to_list(kk), [], ""), Equal.trans(String,
    String.from_list(String.to_list(kk)) ++ "", String.from_list(String.to_list(kk)), kk,
    M2.append_nil(String.from_list(String.to_list(kk))), M2.from_to(kk)))
