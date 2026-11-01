# the cursor's events and position against a derivation of the text
import Base
import ../../src/value.bend as V
import ../../main.bend as Ezjson
import ../../src/lex.bend as Lex
import ../../src/parse.bend as Parse
import ../../src/pull.bend as Pull
import ../../laws/NumOkIsNumberRule.bend as L1
import ../../laws/ParsesExactlyJsonTexts.bend as L2
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ../../laws/defs/GrammarDerivations.bend as D2
import ./ArrayLength.bend as M1
import ./CharacterClasses.bend as M2
import ./DenseTokens.bend as M3
import ./LexemeOrder.bend as M4
import ./LexerPunctuation.bend as M5
import ./NumberCharsAreWordChars.bend as M6
import ./NumberDigits.bend as M7
import ./OwnedParse.bend as M8
import ./ParserReadsTokens.bend as M9
import ./StringPieceLexing.bend as M10
import ./StringTokens.bend as M11
import ./WellFormedCells.bend as M12
import ./WordArithmetic.bend as M13
import ./WordLexing.bend as M14

# WP-P1: parse on a well-formed value's tokens gives the value back, strings
# owned and fixed
law parse_tjr:
  for +val: V.Json
  for h_wf: {V.wf(val) == True{} : Bool}
  {Parse.finish(Parse.run(M12.tj_r(val, V.WVal{}), Parse.P{False{}, None{}, Nil{}})) == Some{M9.canon_r(val,
    V.WVal{})} : Maybe<&2, V.Json>}

def parse_tjr(val, h_wf):
  Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz), Parse.run(M12.tj_r(val, V.WVal{}), Parse.P{False{},
      None{},
    Nil{}}),
    Parse.P{False{}, Some{M9.canon_r(val, V.WVal{})}, Nil{}}, M9.pv_r(val, V.WVal{}, h_wf, False{}, None{}, Nil{},
      V.JNil{})({==}))

# laws/ParsesExactlyJsonTexts.bend: the lexer on a derivation's text

# whether the lexer is between tokens or inside a word
def iw(st: Lex.Lex) -> Bool:
  match st:
    case Lex.Lex{Lex.Idle{}, _, _}:
      True{}
    case Lex.Lex{Lex.Word{}, _, _}:
      True{}
    case _:
      False{}

# a whitespace character between tokens or after a word leaves the lexer
# between tokens, the word pushed
law ws_feed:
  for +ch: Char
  for +st: Lex.Lex
  for h_iw: {iw(st) == True{} : Bool}
  for h_ws: {D1.is_ws(ch) == True{} : Bool}
  {Lex.feed(ch, st) == Lex.Lex{Lex.Idle{}, [], M4.fl(st)} : Lex.Lex}

def ws_feed(ch, st, h_iw, h_ws):
  match ch:
    case Chr{+uu}:
      match st:
        case Lex.Lex{md, +bf, +tk}:
          match md:
            case Lex.Idle{}:
              M4.feed_as(Chr{uu}, Lex.Idle{}, bf, tk, Lex.CSpace{}, M5.ws_a(uu, U32.is_eq(uu, 32), {==}, h_ws))
            case Lex.Word{}:
              M4.feed_as(Chr{uu}, Lex.Word{}, bf, tk, Lex.CSpace{}, M5.ws_a(uu, U32.is_eq(uu, 32), {==}, h_ws))
            case Lex.Str{}:
              M4.no({Lex.feed(Chr{uu}, Lex.Lex{Lex.Str{}, bf, tk}) == Lex.Lex{Lex.Idle{}, [], M4.fl(Lex.Lex{Lex.Str{},
                  bf,
                tk})} : Lex.Lex}, h_iw)
            case Lex.Esc{}:
              M4.no({Lex.feed(Chr{uu}, Lex.Lex{Lex.Esc{}, bf, tk}) == Lex.Lex{Lex.Idle{}, [], M4.fl(Lex.Lex{Lex.Esc{},
                  bf,
                tk})} : Lex.Lex}, h_iw)
            case Lex.Uni{+a1, +a2}:
              M4.no({Lex.feed(Chr{uu}, Lex.Lex{Lex.Uni{a1, a2}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                  M4.fl(Lex.Lex{Lex.Uni{a1,
                a2}, bf, tk})} : Lex.Lex}, h_iw)
            case Lex.Hi{+a1}:
              M4.no({Lex.feed(Chr{uu}, Lex.Lex{Lex.Hi{a1}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                  M4.fl(Lex.Lex{Lex.Hi{a1}, bf,
                tk})} : Lex.Lex}, h_iw)
            case Lex.HiEsc{+a1}:
              M4.no({Lex.feed(Chr{uu}, Lex.Lex{Lex.HiEsc{a1}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                M4.fl(Lex.Lex{Lex.HiEsc{a1}, bf, tk})} : Lex.Lex}, h_iw)
            case Lex.Lo{+a1, +a2, +a3}:
              M4.no({Lex.feed(Chr{uu}, Lex.Lex{Lex.Lo{a1, a2, a3}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                M4.fl(Lex.Lex{Lex.Lo{a1, a2, a3}, bf, tk})} : Lex.Lex}, h_iw)
            case Lex.Bad{}:
              M4.no({Lex.feed(Chr{uu}, Lex.Lex{Lex.Bad{}, bf, tk}) == Lex.Lex{Lex.Idle{}, [], M4.fl(Lex.Lex{Lex.Bad{},
                  bf,
                tk})} : Lex.Lex}, h_iw)

# whitespace between tokens leaves the lexer as it is
law ws_idle:
  for +ww: String
  for +h: {D1.all_ws(ww) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  {Lex.run(String.to_list(ww), Lex.Lex{Lex.Idle{}, [], acc}) == Lex.Lex{Lex.Idle{}, [], acc} : Lex.Lex}

def ws_idle(ww, h, acc):
  match ww:
    case SNil{}:
      {==}
    case SCon{+ch, +tl}:
      Equal.trans(Lex.Lex, Lex.run(String.to_list(tl), Lex.feed(ch, Lex.Lex{Lex.Idle{}, [], acc})),
        Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], acc}), Lex.Lex{Lex.Idle{}, [], acc}, Equal.cong(Lex.Lex,
        Lex.Lex, zz => Lex.run(String.to_list(tl), zz), Lex.feed(ch, Lex.Lex{Lex.Idle{}, [], acc}), Lex.Lex{Lex.Idle{},
        [], acc}, ws_feed(ch, Lex.Lex{Lex.Idle{}, [], acc}, {==}, M4.and_left(D1.is_ws(ch), D1.all_ws(tl), h))),
        ws_idle(tl, M4.and_right(D1.is_ws(ch), D1.all_ws(tl), h), acc))

# a punctuation character after whitespace, between tokens or after a word,
# pushes the word and then its own token
law ws_punct:
  for +ww: String
  for +ch: Char
  for +tt: Lex.Tok
  for ec: {Lex.classify(ch) == Lex.CPunct{tt} : Lex.Class}
  for +st: Lex.Lex
  for +h_iw: {iw(st) == True{} : Bool}
  for +h_w: {D1.all_ws(ww) == True{} : Bool}
  {Lex.feed(ch, Lex.run(String.to_list(ww), st)) == Lex.Lex{Lex.Idle{}, [], tt <> M4.fl(st)} : Lex.Lex}

def ws_punct(ww, ch, tt, ec, st, h_iw, h_w):
  match ww:
    case SNil{}:
      match st:
        case Lex.Lex{md, +bf, +tk}:
          match md:
            case Lex.Idle{}:
              M4.feed_as(ch, Lex.Idle{}, bf, tk, Lex.CPunct{tt}, ec)
            case Lex.Word{}:
              M4.feed_as(ch, Lex.Word{}, bf, tk, Lex.CPunct{tt}, ec)
            case Lex.Str{}:
              M4.no({Lex.feed(ch, Lex.Lex{Lex.Str{}, bf, tk}) == Lex.Lex{Lex.Idle{}, [], tt <> M4.fl(Lex.Lex{Lex.Str{},
                  bf,
                tk})} : Lex.Lex}, h_iw)
            case Lex.Esc{}:
              M4.no({Lex.feed(ch, Lex.Lex{Lex.Esc{}, bf, tk}) == Lex.Lex{Lex.Idle{}, [], tt <> M4.fl(Lex.Lex{Lex.Esc{},
                  bf,
                tk})} : Lex.Lex}, h_iw)
            case Lex.Uni{+a1, +a2}:
              M4.no({Lex.feed(ch, Lex.Lex{Lex.Uni{a1, a2}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                tt <> M4.fl(Lex.Lex{Lex.Uni{a1, a2}, bf, tk})} : Lex.Lex}, h_iw)
            case Lex.Hi{+a1}:
              M4.no({Lex.feed(ch, Lex.Lex{Lex.Hi{a1}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                  tt <> M4.fl(Lex.Lex{Lex.Hi{a1}, bf,
                tk})} : Lex.Lex}, h_iw)
            case Lex.HiEsc{+a1}:
              M4.no({Lex.feed(ch, Lex.Lex{Lex.HiEsc{a1}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                tt <> M4.fl(Lex.Lex{Lex.HiEsc{a1}, bf, tk})} : Lex.Lex}, h_iw)
            case Lex.Lo{+a1, +a2, +a3}:
              M4.no({Lex.feed(ch, Lex.Lex{Lex.Lo{a1, a2, a3}, bf, tk}) == Lex.Lex{Lex.Idle{}, [],
                tt <> M4.fl(Lex.Lex{Lex.Lo{a1, a2, a3}, bf, tk})} : Lex.Lex}, h_iw)
            case Lex.Bad{}:
              M4.no({Lex.feed(ch, Lex.Lex{Lex.Bad{}, bf, tk}) == Lex.Lex{Lex.Idle{}, [], tt <> M4.fl(Lex.Lex{Lex.Bad{},
                  bf,
                tk})} : Lex.Lex}, h_iw)
    case SCon{+c1, +tl}:
      Equal.trans(Lex.Lex, Lex.feed(ch, Lex.run(String.to_list(tl), Lex.feed(c1, st))), Lex.feed(ch,
        Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], M4.fl(st)})), Lex.Lex{Lex.Idle{}, [], tt <> M4.fl(st)},
        Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.feed(ch, Lex.run(String.to_list(tl), zz)), Lex.feed(c1, st),
        Lex.Lex{Lex.Idle{}, [], M4.fl(st)}, ws_feed(c1, st, h_iw, M4.and_left(D1.is_ws(c1), D1.all_ws(tl), h_w))),
        Equal.trans(Lex.Lex, Lex.feed(ch, Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], M4.fl(st)})), Lex.feed(ch,
        Lex.Lex{Lex.Idle{}, [], M4.fl(st)}), Lex.Lex{Lex.Idle{}, [], tt <> M4.fl(st)}, Equal.cong(Lex.Lex, Lex.Lex,
        zz => Lex.feed(ch, zz), Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], M4.fl(st)}), Lex.Lex{Lex.Idle{}, [],
        M4.fl(st)}, ws_idle(tl, M4.and_right(D1.is_ws(c1), D1.all_ws(tl), h_w), M4.fl(st))), M4.feed_as(ch, Lex.Idle{},
            [],
        M4.fl(st), Lex.CPunct{tt}, ec)))

# the end of the text after whitespace, between tokens or after a word,
# pushes the word
law ws_fin:
  for +ww: String
  for +st: Lex.Lex
  for +h_iw: {iw(st) == True{} : Bool}
  for +h_w: {D1.all_ws(ww) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list(ww), st)) == List.reverse(&2, Lex.Tok, M4.fl(st)) : List<&2, Lex.Tok>}

def ws_fin(ww, st, h_iw, h_w):
  match ww:
    case SNil{}:
      match st:
        case Lex.Lex{md, +bf, +tk}:
          match md:
            case Lex.Idle{}:
              {==}
            case Lex.Word{}:
              {==}
            case Lex.Str{}:
              M4.no({Lex.finish(Lex.Lex{Lex.Str{}, bf, tk}) == List.reverse(&2, Lex.Tok, M4.fl(Lex.Lex{Lex.Str{}, bf,
                tk})) : List<&2, Lex.Tok>}, h_iw)
            case Lex.Esc{}:
              M4.no({Lex.finish(Lex.Lex{Lex.Esc{}, bf, tk}) == List.reverse(&2, Lex.Tok, M4.fl(Lex.Lex{Lex.Esc{}, bf,
                tk})) : List<&2, Lex.Tok>}, h_iw)
            case Lex.Uni{+a1, +a2}:
              M4.no({Lex.finish(Lex.Lex{Lex.Uni{a1, a2}, bf, tk}) == List.reverse(&2, Lex.Tok,
                  M4.fl(Lex.Lex{Lex.Uni{a1, a2},
                bf, tk})) : List<&2, Lex.Tok>}, h_iw)
            case Lex.Hi{+a1}:
              M4.no({Lex.finish(Lex.Lex{Lex.Hi{a1}, bf, tk}) == List.reverse(&2, Lex.Tok, M4.fl(Lex.Lex{Lex.Hi{a1}, bf,
                tk})) : List<&2, Lex.Tok>}, h_iw)
            case Lex.HiEsc{+a1}:
              M4.no({Lex.finish(Lex.Lex{Lex.HiEsc{a1}, bf, tk}) == List.reverse(&2, Lex.Tok,
                  M4.fl(Lex.Lex{Lex.HiEsc{a1}, bf,
                tk})) : List<&2, Lex.Tok>}, h_iw)
            case Lex.Lo{+a1, +a2, +a3}:
              M4.no({Lex.finish(Lex.Lex{Lex.Lo{a1, a2, a3}, bf, tk}) == List.reverse(&2, Lex.Tok,
                  M4.fl(Lex.Lex{Lex.Lo{a1,
                a2, a3}, bf, tk})) : List<&2, Lex.Tok>}, h_iw)
            case Lex.Bad{}:
              M4.no({Lex.finish(Lex.Lex{Lex.Bad{}, bf, tk}) == List.reverse(&2, Lex.Tok, M4.fl(Lex.Lex{Lex.Bad{}, bf,
                tk})) : List<&2, Lex.Tok>}, h_iw)
    case SCon{+c1, +tl}:
      Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(tl), Lex.feed(c1, st))),
        Lex.finish(Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], M4.fl(st)})), Lex.finish(Lex.Lex{Lex.Idle{}, [],
        M4.fl(st)}), Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(Lex.run(String.to_list(tl), zz)),
        Lex.feed(c1, st), Lex.Lex{Lex.Idle{}, [], M4.fl(st)}, ws_feed(c1, st, h_iw, M4.and_left(D1.is_ws(c1),
        D1.all_ws(tl), h_w))), Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz),
        Lex.run(String.to_list(tl), Lex.Lex{Lex.Idle{}, [], M4.fl(st)}), Lex.Lex{Lex.Idle{}, [], M4.fl(st)}, ws_idle(tl,
        M4.and_right(D1.is_ws(c1), D1.all_ws(tl), h_w), M4.fl(st))))

# a string's pieces, read inside it, whatever tokens came before
law spell_in:
  for +ps: List<&2, D2.Piece>
  for +h: {D2.spell_ok(ps) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  {Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], acc}) == Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []), acc} : Lex.Lex}

def spell_in(ps, h, acc):
  Equal.trans(Lex.Lex, Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], acc}),
    M2.lex.app(Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], []}), acc), Lex.Lex{Lex.Str{},
    List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), acc}, M8.run_pass(String.to_list(D2.spell(ps)),
    Lex.Lex{Lex.Str{}, [], []}, acc), Equal.cong(Lex.Lex, Lex.Lex, zz => M2.lex.app(zz, acc),
    Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], []}), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []), []}, M10.spell_lex(ps, h, [])))

# a well spelled string between tokens is its token
law str_in:
  for +ps: List<&2, D2.Piece>
  for +h: {D2.spell_ok(ps) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  {Lex.run(String.to_list("\"" ++ D2.spell(ps) ++ "\""), Lex.Lex{Lex.Idle{}, [], acc}) == Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{D2.spelled(ps)} <> acc} : Lex.Lex}

def str_in(ps, h, acc):
  Equal.trans(Lex.Lex, Lex.run(String.to_list("\"" ++ D2.spell(ps) ++ "\""), Lex.Lex{Lex.Idle{}, [], acc}),
    Lex.run(String.to_list(D2.spell(ps) ++ "\""), Lex.Lex{Lex.Str{}, [], acc}), Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{D2.spelled(ps)} <> acc}, M11.seq("\"", D2.spell(ps) ++ "\"", Lex.Lex{Lex.Idle{}, [], acc},
    Lex.Lex{Lex.Str{}, [], acc}, {==}), Equal.trans(Lex.Lex, Lex.run(String.to_list(D2.spell(ps) ++ "\""),
    Lex.Lex{Lex.Str{}, [], acc}), Lex.run(String.to_list("\""), Lex.run(String.to_list(D2.spell(ps)),
    Lex.Lex{Lex.Str{}, [], acc})), Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> acc}, M11.run_app(D2.spell(ps),
    "\"", Lex.Lex{Lex.Str{}, [], acc}), Equal.trans(Lex.Lex, Lex.run(String.to_list("\""),
    Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], acc})), Lex.run(String.to_list("\""),
    Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), acc}), Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{D2.spelled(ps)} <> acc}, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list("\""), zz),
    Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{}, [], acc}), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []), acc}, spell_in(ps, h, acc)), Equal.trans(Lex.Lex,
    Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []),
    acc}), Lex.Lex{Lex.Idle{}, [], Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)),
    []))} <> acc}, Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> acc}, {==}, Equal.cong(String, Lex.Lex,
    zz => Lex.Lex{Lex.Idle{}, [], Lex.TStr{zz} <> acc}, Lex.text(List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), [])), D2.spelled(ps), M10.text_k(D2.spelled(ps)))))))

# the lexer on three strings, the last split off
law run_assoc:
  for +aa: String
  for +bb: String
  for +cc: String
  for +st: Lex.Lex
  {Lex.run(String.to_list(aa ++ bb ++ cc), st) == Lex.run(String.to_list(cc), Lex.run(String.to_list(aa ++ bb),
    st)) : Lex.Lex}

def run_assoc(aa, bb, cc, st):
  Equal.trans(Lex.Lex, Lex.run(String.to_list(aa ++ bb ++ cc), st), Lex.run(String.to_list(bb ++ cc),
    Lex.run(String.to_list(aa), st)), Lex.run(String.to_list(cc), Lex.run(String.to_list(aa ++ bb), st)),
        M11.run_app(aa,
    bb ++ cc, st), Equal.trans(Lex.Lex, Lex.run(String.to_list(bb ++ cc), Lex.run(String.to_list(aa), st)),
    Lex.run(String.to_list(cc), Lex.run(String.to_list(bb), Lex.run(String.to_list(aa), st))),
    Lex.run(String.to_list(cc), Lex.run(String.to_list(aa ++ bb), st)), M11.run_app(bb, cc, Lex.run(String.to_list(aa),
    st)), Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(cc), zz), Lex.run(String.to_list(bb),
    Lex.run(String.to_list(aa), st)), Lex.run(String.to_list(aa ++ bb), st), Equal.sym(Lex.Lex,
    Lex.run(String.to_list(aa ++ bb), st), Lex.run(String.to_list(bb), Lex.run(String.to_list(aa), st)), M11.run_app(aa,
    bb, st)))))

# an object member's name, colon and whitespace, between tokens, are their
# tokens
law mem_in:
  for +ps: List<&2, D2.Piece>
  for +w1: String
  for +w2: String
  for +tt: String
  for +h_ps: {D2.spell_ok(ps) == True{} : Bool}
  for +h_1: {D1.all_ws(w1) == True{} : Bool}
  for +h_2: {D1.all_ws(w2) == True{} : Bool}
  for +bb: List<&2, Lex.Tok>
  {Lex.run(String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{}, [],
    bb}) == Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}) : Lex.Lex}

def mem_in(ps, w1, w2, tt, h_ps, h_1, h_2, bb):
  Equal.trans(Lex.Lex, Lex.run(String.to_list("\"" ++ D2.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ tt),
    Lex.Lex{Lex.Idle{}, [], bb}), Lex.run(String.to_list(D2.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ tt),
    Lex.Lex{Lex.Str{}, [], bb}), Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), M11.seq("\"", D2.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ tt,
    Lex.Lex{Lex.Idle{}, [], bb}, Lex.Lex{Lex.Str{}, [], bb}, {==}), Equal.trans(Lex.Lex,
    Lex.run(String.to_list(D2.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Str{}, [], bb}),
    Lex.run(String.to_list("\"" ++ w1 ++ ":" ++ w2 ++ tt), Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{},
    [], bb})), Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}),
    M11.run_app(D2.spell(ps), "\"" ++ w1 ++ ":" ++ w2 ++ tt, Lex.Lex{Lex.Str{}, [], bb}), Equal.trans(Lex.Lex,
    Lex.run(String.to_list("\"" ++ w1 ++ ":" ++ w2 ++ tt), Lex.run(String.to_list(D2.spell(ps)), Lex.Lex{Lex.Str{},
    [], bb})), Lex.run(String.to_list("\"" ++ w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []), bb}), Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), Equal.cong(Lex.Lex, Lex.Lex,
    zz => Lex.run(String.to_list("\"" ++ w1 ++ ":" ++ w2 ++ tt), zz), Lex.run(String.to_list(D2.spell(ps)),
    Lex.Lex{Lex.Str{}, [], bb}), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []),
    bb}, spell_in(ps, h_ps, bb)), Equal.trans(Lex.Lex, Lex.run(String.to_list("\"" ++ w1 ++ ":" ++ w2 ++ tt),
    Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), bb}),
    Lex.run(String.to_list(w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{}, [], Lex.TStr{Lex.text(List.reverse.go(&2, Char,
    String.to_list(D2.spelled(ps)), []))} <> bb}), Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), M11.seq("\"", w1 ++ ":" ++ w2 ++ tt, Lex.Lex{Lex.Str{},
    List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []), bb}, Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []))} <> bb}, {==}),
    Equal.trans(Lex.Lex, Lex.run(String.to_list(w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), []))} <> bb}),
    Lex.run(String.to_list(w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> bb}),
    Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}),
    Equal.cong(String, Lex.Lex, zz => Lex.run(String.to_list(w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{zz} <> bb}), Lex.text(List.reverse.go(&2, Char, String.to_list(D2.spelled(ps)), [])), D2.spelled(ps),
    M10.text_k(D2.spelled(ps))), Equal.trans(Lex.Lex, Lex.run(String.to_list(w1 ++ ":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{},
    [], Lex.TStr{D2.spelled(ps)} <> bb}), Lex.run(String.to_list(":" ++ w2 ++ tt), Lex.run(String.to_list(w1),
    Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> bb})), Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), M11.run_app(w1, ":" ++ w2 ++ tt, Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{D2.spelled(ps)} <> bb}), Equal.trans(Lex.Lex, Lex.run(String.to_list(":" ++ w2 ++ tt),
    Lex.run(String.to_list(w1), Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> bb})),
    Lex.run(String.to_list(":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> bb}),
    Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}),
    Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(":" ++ w2 ++ tt), zz), Lex.run(String.to_list(w1),
    Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> bb}), Lex.Lex{Lex.Idle{}, [],
    Lex.TStr{D2.spelled(ps)} <> bb}, ws_idle(w1, h_1, Lex.TStr{D2.spelled(ps)} <> bb)), Equal.trans(Lex.Lex,
    Lex.run(String.to_list(":" ++ w2 ++ tt), Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> bb}),
    Lex.run(String.to_list(w2 ++ tt), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}),
    Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), M11.seq(":",
    w2 ++ tt, Lex.Lex{Lex.Idle{}, [], Lex.TStr{D2.spelled(ps)} <> bb}, Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}, {==}), Equal.trans(Lex.Lex, Lex.run(String.to_list(w2 ++ tt),
    Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), Lex.run(String.to_list(tt),
    Lex.run(String.to_list(w2), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb})),
    Lex.run(String.to_list(tt), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}),
        M11.run_app(w2,
    tt, Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), Equal.cong(Lex.Lex, Lex.Lex,
    zz => Lex.run(String.to_list(tt), zz), Lex.run(String.to_list(w2), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}), Lex.Lex{Lex.Idle{}, [],
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb}, ws_idle(w2, h_2,
    Lex.TColon{} <> Lex.TStr{D2.spelled(ps)} <> bb)))))))))))

# the lexer's state after a value's text, from between tokens: inside a word,
# or the value's tokens pushed
def gend(gg: D2.Gv, acc: List<&2, Lex.Tok>) -> Lex.Lex:
  match gg:
    case D2.GWord{w}:
      Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, String.to_list(w), []), acc}
    case other:
      Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(other), V.WVal{}), acc)}

# after a value's text the lexer is between tokens or inside a word
law iw_gend:
  for +gg: D2.Gv
  for +acc: List<&2, Lex.Tok>
  {iw(gend(gg, acc)) == True{} : Bool}

def iw_gend(gg, _acc):
  match gg:
    case D2.GWord{+a1}:
      {==}
    case D2.GStr{+a1}:
      {==}
    case D2.GArr0{+a1}:
      {==}
    case D2.GArr{+a1, +a2, +a3, +a4}:
      {==}
    case D2.GObj0{+a1}:
      {==}
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      {==}
    case D2.GEnd{}:
      {==}
    case D2.GNext{+a1, +a2, +a3, +a4}:
      {==}
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      {==}

# a literal name or a number is one word
law tjw.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +w: String
  for e1: {String.eq(w, "null") == b1 : Bool}
  for e2: {String.eq(w, "true") == b2 : Bool}
  for e3: {String.eq(w, "false") == b3 : Bool}
  {M12.tj_r(Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3,
    V.JBool{False{}}, V.JNum{w}))), V.WVal{}) == [Lex.TWord{w}] : List<&2, Lex.Tok>}

def tjw.at(b1, b2, b3, w, e1, e2, e3):
  match b1:
    case True{}:
      Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TWord{zz}], "null", w, Equal.sym(String, w, "null",
        M6.str_eq_sound(w, "null", e1)))
    case False{}:
      match b2:
        case True{}:
          Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TWord{zz}], "true", w, Equal.sym(String, w, "true",
            M6.str_eq_sound(w, "true", e2)))
        case False{}:
          match b3:
            case True{}:
              Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TWord{zz}], "false", w, Equal.sym(String, w, "false",
                M6.str_eq_sound(w, "false", e3)))
            case False{}:
              {==}

# a word's value reads back as the word
law tjw:
  for +w: String
  {M12.tj_r(L2.g.word(w), V.WVal{}) == [Lex.TWord{w}] : List<&2, Lex.Tok>}

def tjw(w):
  tjw.at(String.eq(w, "null"), String.eq(w, "true"), String.eq(w, "false"), w, {==}, {==}, {==})

# after a value's text the lexer holds the value's tokens, its word pushed
law fl_gend:
  for +gg: D2.Gv
  for +acc: List<&2, Lex.Tok>
  {M4.fl(gend(gg, acc)) == List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(gg), V.WVal{}), acc) : List<&2, Lex.Tok>}

def fl_gend(gg, acc):
  match gg:
    case D2.GWord{+w}:
      Equal.trans(List<&2, Lex.Tok>, Lex.TWord{Lex.text(List.reverse.go(&2, Char, String.to_list(w), []))} <> acc,
        Lex.TWord{w} <> acc, List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.word(w), V.WVal{}), acc), Equal.cong(String,
        List<&2, Lex.Tok>, zz => Lex.TWord{zz} <> acc, Lex.text(List.reverse.go(&2, Char, String.to_list(w), [])), w,
        M4.word_text(w)), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => List.reverse.go(&2, Lex.Tok, zz, acc),
        [Lex.TWord{w}], M12.tj_r(L2.g.word(w), V.WVal{}), Equal.sym(List<&2, Lex.Tok>, M12.tj_r(L2.g.word(w), V.WVal{}),
        [Lex.TWord{w}], tjw(w))))
    case D2.GStr{+a1}:
      {==}
    case D2.GArr0{+a1}:
      {==}
    case D2.GArr{+a1, +a2, +a3, +a4}:
      {==}
    case D2.GObj0{+a1}:
      {==}
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      {==}
    case D2.GEnd{}:
      {==}
    case D2.GNext{+a1, +a2, +a3, +a4}:
      {==}
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      {==}

# a literal name or a number, read from between tokens, is a word
law lex_lit.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +w: String
  for e1: {String.eq(w, "null") == b1 : Bool}
  for e2: {String.eq(w, "true") == b2 : Bool}
  for e3: {String.eq(w, "false") == b3 : Bool}
  for h: {Bool.or(b1, Bool.or(b2, Bool.or(b3, D1.number(String.to_list(w))))) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  {Lex.run(String.to_list(w), Lex.Lex{Lex.Idle{}, [], acc}) == Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char,
    String.to_list(w), []), acc} : Lex.Lex}

def lex_lit.at(b1, b2, b3, w, e1, e2, e3, h, acc):
  match b1:
    case True{}:
      ek = Equal.sym(String, w, "null", M6.str_eq_sound(w, "null", e1))
      %ek : {Lex.run(String.to_list(_), Lex.Lex{Lex.Idle{}, [], acc}) == Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char,
        String.to_list(_), []), acc} : Lex.Lex}
      {==}
    case False{}:
      match b2:
        case True{}:
          ek = Equal.sym(String, w, "true", M6.str_eq_sound(w, "true", e2))
          %ek : {Lex.run(String.to_list(_), Lex.Lex{Lex.Idle{}, [], acc}) == Lex.Lex{Lex.Word{}, List.reverse.go(&2,
            Char, String.to_list(_), []), acc} : Lex.Lex}
          {==}
        case False{}:
          match b3:
            case True{}:
              ek = Equal.sym(String, w, "false", M6.str_eq_sound(w, "false", e3))
              %ek : {Lex.run(String.to_list(_), Lex.Lex{Lex.Idle{}, [], acc}) == Lex.Lex{Lex.Word{},
                List.reverse.go(&2, Char, String.to_list(_), []), acc} : Lex.Lex}
              {==}
            case False{}:
              M3.lex_numl(String.to_list(w), h, acc)

# the tokens of an object's cells after a member
def co(rr: D2.Gv) -> List<&2, Lex.Tok>:
  match rr:
    case D2.GEnd{}:
      []
    case other:
      Lex.TComma{} <> M12.tj_r(L2.g.val(other), V.WObj{})

# an element and the cells after it
law ct_eq:
  for +vh: V.Json
  for +rr: D2.Gv
  for +h: {D2.g.ok(rr, D2.GKArr{}) == True{} : Bool}
  {M12.tj_r(V.JCons{vh, L2.g.val(rr)}, V.WArr{}) == List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
      M12.ct(rr)) : List<&2,
    Lex.Tok>}

def ct_eq(vh, rr, h):
  match rr:
    case D2.GWord{+a1}:
      M4.no({M12.tj_r(V.JCons{vh, L2.g.val(D2.GWord{a1})}, V.WArr{}) == List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
        M12.ct(D2.GWord{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GStr{+a1}:
      M4.no({M12.tj_r(V.JCons{vh, L2.g.val(D2.GStr{a1})}, V.WArr{}) == List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
        M12.ct(D2.GStr{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GArr0{+a1}:
      M4.no({M12.tj_r(V.JCons{vh, L2.g.val(D2.GArr0{a1})}, V.WArr{}) == List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
        M12.ct(D2.GArr0{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GArr{+a1, +a2, +a3, +a4}:
      M4.no({M12.tj_r(V.JCons{vh, L2.g.val(D2.GArr{a1, a2, a3, a4})}, V.WArr{}) == List.append(&2, Lex.Tok, M12.tj_r(vh,
        V.WVal{}), M12.ct(D2.GArr{a1, a2, a3, a4})) : List<&2, Lex.Tok>}, h)
    case D2.GObj0{+a1}:
      M4.no({M12.tj_r(V.JCons{vh, L2.g.val(D2.GObj0{a1})}, V.WArr{}) == List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
        M12.ct(D2.GObj0{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      M4.no({M12.tj_r(V.JCons{vh, L2.g.val(D2.GObj{a1, a2, a3, a4, a5, a6, a7})}, V.WArr{}) == List.append(&2, Lex.Tok,
        M12.tj_r(vh, V.WVal{}), M12.ct(D2.GObj{a1, a2, a3, a4, a5, a6, a7})) : List<&2, Lex.Tok>}, h)
    case D2.GEnd{}:
      Equal.sym(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}), []), M12.tj_r(vh, V.WVal{}),
        M3.lapp_nil(M12.tj_r(vh, V.WVal{})))
    case D2.GNext{+a1, +a2, +a3, +a4}:
      {==}
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      M4.no({M12.tj_r(V.JCons{vh, L2.g.val(D2.GNextM{a1, a2, a3, a4, a5, a6, a7})}, V.WArr{}) == List.append(&2,
          Lex.Tok,
        M12.tj_r(vh, V.WVal{}), M12.ct(D2.GNextM{a1, a2, a3, a4, a5, a6, a7})) : List<&2, Lex.Tok>}, h)

# a member and the cells after it
law co_eq:
  for +sp: String
  for +vh: V.Json
  for +rr: D2.Gv
  for +h: {D2.g.ok(rr, D2.GKObj{}) == True{} : Bool}
  {M12.tj_r(V.JPair{sp, vh, L2.g.val(rr)}, V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
      M12.tj_r(vh,
    V.WVal{}), co(rr)) : List<&2, Lex.Tok>}

def co_eq(sp, vh, rr, h):
  match rr:
    case D2.GWord{+a1}:
      M4.no({M12.tj_r(V.JPair{sp, vh, L2.g.val(D2.GWord{a1})},
        V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
        co(D2.GWord{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GStr{+a1}:
      M4.no({M12.tj_r(V.JPair{sp, vh, L2.g.val(D2.GStr{a1})},
          V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2,
        Lex.Tok, M12.tj_r(vh, V.WVal{}), co(D2.GStr{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GArr0{+a1}:
      M4.no({M12.tj_r(V.JPair{sp, vh, L2.g.val(D2.GArr0{a1})},
        V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
        co(D2.GArr0{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GArr{+a1, +a2, +a3, +a4}:
      M4.no({M12.tj_r(V.JPair{sp, vh, L2.g.val(D2.GArr{a1, a2, a3, a4})},
        V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}), co(D2.GArr{a1, a2,
        a3, a4})) : List<&2, Lex.Tok>}, h)
    case D2.GObj0{+a1}:
      M4.no({M12.tj_r(V.JPair{sp, vh, L2.g.val(D2.GObj0{a1})},
        V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}),
        co(D2.GObj0{a1})) : List<&2, Lex.Tok>}, h)
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      M4.no({M12.tj_r(V.JPair{sp, vh, L2.g.val(D2.GObj{a1, a2, a3, a4, a5, a6, a7})},
        V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}), co(D2.GObj{a1, a2,
        a3, a4, a5, a6, a7})) : List<&2, Lex.Tok>}, h)
    case D2.GEnd{}:
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => Lex.TStr{sp} <> Lex.TColon{} <> zz, M12.tj_r(vh, V.WVal{}),
        List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}), []), Equal.sym(List<&2, Lex.Tok>, List.append(&2, Lex.Tok,
        M12.tj_r(vh, V.WVal{}), []), M12.tj_r(vh, V.WVal{}), M3.lapp_nil(M12.tj_r(vh, V.WVal{}))))
    case D2.GNext{+a1, +a2, +a3, +a4}:
      M4.no({M12.tj_r(V.JPair{sp, vh, L2.g.val(D2.GNext{a1, a2, a3, a4})},
        V.WObj{}) == Lex.TStr{sp} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(vh, V.WVal{}), co(D2.GNext{a1,
            a2,
        a3, a4})) : List<&2, Lex.Tok>}, h)
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      {==}

# what lexg says: a value's text read from between tokens; or an array's or
# object's cells after an element, with the whitespace before them and the
# closing bracket after them, read from between tokens or inside a word
def lgg(+gg: D2.Gv, kk: D2.GK, +acc: List<&2, Lex.Tok>, +ww: String, +st: Lex.Lex) -> Type:
  match kk:
    case D2.GKVal{}:
      {Lex.run(String.to_list(D2.g.text(gg)), Lex.Lex{Lex.Idle{}, [], acc}) == gend(gg, acc) : Lex.Lex}
    case D2.GKArr{}:
      {iw(st) == True{} : Bool} -> {D1.all_ws(ww) == True{} : Bool} ->
        {Lex.run(String.to_list(ww ++ D2.g.text(gg) ++ "]"), st) == Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(gg), M4.fl(st))} : Lex.Lex}
    case D2.GKObj{}:
      {iw(st) == True{} : Bool} -> {D1.all_ws(ww) == True{} : Bool} ->
        {Lex.run(String.to_list(ww ++ D2.g.text(gg) ++ "}"), st) == Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(gg), M4.fl(st))} : Lex.Lex}

# a derivation's text, read by the character lexer: a value pushes its
# tokens, and an array's or object's cells push theirs and the closing bracket
law lexg:
  for +gg: D2.Gv
  for kk: D2.GK
  for +h: {D2.g.ok(gg, kk) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  for +ww: String
  for +st: Lex.Lex
  lgg(gg, kk, acc, ww, st)

def lexg(gg, kk, h, acc, ww, st):
  match gg:
    case D2.GWord{+a1}:
      match kk:
        case D2.GKVal{}:
          lex_lit.at(String.eq(a1, "null"), String.eq(a1, "true"), String.eq(a1, "false"), a1, {==}, {==}, {==}, h, acc)
        case D2.GKArr{}:
          M4.no(lgg(D2.GWord{a1}, D2.GKArr{}, acc, ww, st), h)
        case D2.GKObj{}:
          M4.no(lgg(D2.GWord{a1}, D2.GKObj{}, acc, ww, st), h)
    case D2.GStr{+a1}:
      match kk:
        case D2.GKVal{}:
          str_in(a1, h, acc)
        case D2.GKArr{}:
          M4.no(lgg(D2.GStr{a1}, D2.GKArr{}, acc, ww, st), h)
        case D2.GKObj{}:
          M4.no(lgg(D2.GStr{a1}, D2.GKObj{}, acc, ww, st), h)
    case D2.GArr0{+a1}:
      match kk:
        case D2.GKVal{}:
          Equal.trans(Lex.Lex, Lex.run(String.to_list("[" ++ a1 ++ "]"), Lex.Lex{Lex.Idle{}, [], acc}),
            Lex.run(String.to_list(a1 ++ "]"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> Lex.TOpenArr{} <> acc}, M11.seq("[", a1 ++ "]", Lex.Lex{Lex.Idle{}, [], acc},
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}, {==}), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a1 ++ "]"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}),
            Lex.run(String.to_list("]"), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})),
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> Lex.TOpenArr{} <> acc}, M11.run_app(a1, "]", Lex.Lex{Lex.Idle{},
                [],
            Lex.TOpenArr{} <> acc}), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(a1),
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})), Lex.run(String.to_list("]"), Lex.Lex{Lex.Idle{}, [],
            Lex.TOpenArr{} <> acc}), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> Lex.TOpenArr{} <> acc},
            Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list("]"), zz), Lex.run(String.to_list(a1),
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc},
            ws_idle(a1, h, Lex.TOpenArr{} <> acc)), {==})))
        case D2.GKArr{}:
          M4.no(lgg(D2.GArr0{a1}, D2.GKArr{}, acc, ww, st), h)
        case D2.GKObj{}:
          M4.no(lgg(D2.GArr0{a1}, D2.GKObj{}, acc, ww, st), h)
    case D2.GArr{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          Equal.trans(Lex.Lex, Lex.run(String.to_list("[" ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"),
            Lex.Lex{Lex.Idle{}, [], acc}),
            Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"), Lex.Lex{Lex.Idle{}, [],
            Lex.TOpenArr{} <> acc}), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)},
            M11.seq("[", a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]", Lex.Lex{Lex.Idle{}, [], acc},
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}, {==}), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"), Lex.Lex{Lex.Idle{}, [],
            Lex.TOpenArr{} <> acc}), Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"),
            Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})), Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)},
            V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, M11.run_app(a1,
            D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]", Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}),
            Equal.trans(Lex.Lex, Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"),
            Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})),
            Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"), Lex.Lex{Lex.Idle{}, [],
            Lex.TOpenArr{} <> acc}), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)},
            Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"),
            zz), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}), Lex.Lex{Lex.Idle{}, [],
            Lex.TOpenArr{} <> acc}, ws_idle(a1, M4.and_left(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h), Lex.TOpenArr{} <> acc)), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4) ++ "]"), Lex.Lex{Lex.Idle{}, [],
            Lex.TOpenArr{} <> acc}), Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"),
            Lex.run(String.to_list(D2.g.text(a2)), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})),
            Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, M11.run_app(D2.g.text(a2),
            a3 ++ D2.g.text(a4) ++ "]", Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"), Lex.run(String.to_list(D2.g.text(a2)),
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})), Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"),
            gend(a2, Lex.TOpenArr{} <> acc)), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2,
            Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), [Lex.TCloseArr{}]),
            Lex.TOpenArr{} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"), zz), Lex.run(String.to_list(D2.g.text(a2)),
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}), gend(a2, Lex.TOpenArr{} <> acc), lexg(a2, D2.GKVal{},
            M4.and_left(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})),
            M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{}))), h)), Lex.TOpenArr{} <> acc, ww, st)), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"), gend(a2, Lex.TOpenArr{} <> acc)), Lex.Lex{Lex.Idle{},
            [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), M4.fl(gend(a2, Lex.TOpenArr{} <> acc)))},
            Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, lexg(a4, D2.GKArr{},
            M4.and_right(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h))), acc, a3, gend(a2,
            Lex.TOpenArr{} <> acc))(iw_gend(a2, Lex.TOpenArr{} <> acc), M4.and_left(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{}), M4.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h)))), Equal.trans(Lex.Lex, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), M4.fl(gend(a2, Lex.TOpenArr{} <> acc)))},
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), List.reverse.go(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), Lex.TOpenArr{} <> acc))}, Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)},
            V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
            zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), zz)},
                M4.fl(gend(a2,
            Lex.TOpenArr{} <> acc)), List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}),
            Lex.TOpenArr{} <> acc), fl_gend(a2, Lex.TOpenArr{} <> acc)), Equal.trans(Lex.Lex, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), List.reverse.go(&2, Lex.Tok,
                M12.tj_r(L2.g.val(a2),
            V.WVal{}), Lex.TOpenArr{} <> acc))}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2,
            Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)), Lex.TOpenArr{} <> acc)},
            Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, Equal.cong(List<&2, Lex.Tok>,
            Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> zz}, List.reverse.go(&2, Lex.Tok, M12.ct(a4),
            List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), Lex.TOpenArr{} <> acc)), List.reverse.go(&2,
            Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)), Lex.TOpenArr{} <> acc),
            Equal.sym(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2),
            V.WVal{}), M12.ct(a4)), Lex.TOpenArr{} <> acc), List.reverse.go(&2, Lex.Tok, M12.ct(a4), List.reverse.go(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), Lex.TOpenArr{} <> acc)), M12.rev_app(M12.tj_r(L2.g.val(a2),
                V.WVal{}),
            M12.ct(a4), Lex.TOpenArr{} <> acc))), Equal.trans(Lex.Lex, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}),
            M12.ct(a4)), Lex.TOpenArr{} <> acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2,
                Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TOpenArr{} <> acc)}, Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)},
            V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
            zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, zz, Lex.TOpenArr{} <> acc)},
            List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)), M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), Equal.sym(List<&2, Lex.Tok>, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)},
            V.WArr{}), List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)), ct_eq(L2.g.val(a2), a4,
            M4.and_right(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h)))))), Equal.cong(List<&2,
            Lex.Tok>, Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [], zz}, Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TOpenArr{} <> acc), List.reverse.go(&2,
            Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}),
            [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc), Equal.sym(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok,
            List.append(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), [Lex.TCloseArr{}]),
            Lex.TOpenArr{} <> acc), Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), Lex.TOpenArr{} <> acc), M10.rev_snoc_t(M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), Lex.TCloseArr{}, Lex.TOpenArr{} <> acc))))))))))))
        case D2.GKArr{}:
          M4.no(lgg(D2.GArr{a1, a2, a3, a4}, D2.GKArr{}, acc, ww, st), h)
        case D2.GKObj{}:
          M4.no(lgg(D2.GArr{a1, a2, a3, a4}, D2.GKObj{}, acc, ww, st), h)
    case D2.GObj0{+a1}:
      match kk:
        case D2.GKVal{}:
          Equal.trans(Lex.Lex, Lex.run(String.to_list("{" ++ a1 ++ "}"), Lex.Lex{Lex.Idle{}, [], acc}),
            Lex.run(String.to_list(a1 ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> Lex.TOpenObj{} <> acc}, M11.seq("{", a1 ++ "}", Lex.Lex{Lex.Idle{}, [], acc},
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}, {==}), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a1 ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
            Lex.run(String.to_list("}"), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc})),
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> Lex.TOpenObj{} <> acc}, M11.run_app(a1, "}", Lex.Lex{Lex.Idle{},
                [],
            Lex.TOpenObj{} <> acc}), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(a1),
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc})), Lex.run(String.to_list("}"), Lex.Lex{Lex.Idle{}, [],
            Lex.TOpenObj{} <> acc}), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> Lex.TOpenObj{} <> acc},
            Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list("}"), zz), Lex.run(String.to_list(a1),
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc},
            ws_idle(a1, h, Lex.TOpenObj{} <> acc)), {==})))
        case D2.GKArr{}:
          M4.no(lgg(D2.GObj0{a1}, D2.GKArr{}, acc, ww, st), h)
        case D2.GKObj{}:
          M4.no(lgg(D2.GObj0{a1}, D2.GKObj{}, acc, ww, st), h)
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          Equal.trans(Lex.Lex,
            Lex.run(String.to_list("{" ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++
            a6 ++ D2.g.text(a7) ++ "}"), Lex.Lex{Lex.Idle{}, [], acc}),
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}), Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, M11.seq("{",
            a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}",
            Lex.Lex{Lex.Idle{}, [], acc}, Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}, {==}), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7) ++ "}"), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc})),
            Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
            M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]),
            Lex.TOpenObj{} <> acc)}, M11.run_app(a1,
            "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}",
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}), Equal.trans(Lex.Lex,
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7) ++ "}"), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc})),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}), Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7) ++ "}"), zz), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
            Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}, ws_idle(a1, M4.and_left(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h), Lex.TOpenObj{} <> acc)),
            Equal.trans(Lex.Lex,
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
            Lex.run(String.to_list(D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}"), Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc}), Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, mem_in(a2, a3, a4,
            D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}", M4.and_left(D2.spell_ok(a2), Bool.and(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))))), M4.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))))), h)), M4.and_left(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))), M4.and_left(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))),
            M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))), Lex.TOpenObj{} <> acc),
            Equal.trans(Lex.Lex, Lex.run(String.to_list(D2.g.text(a5) ++ a6 ++ D2.g.text(a7) ++ "}"),
            Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc}),
            Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), Lex.run(String.to_list(D2.g.text(a5)),
            Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc})),
            Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
            M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]),
            Lex.TOpenObj{} <> acc)}, M11.run_app(D2.g.text(a5), a6 ++ D2.g.text(a7) ++ "}", Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc}), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), Lex.run(String.to_list(D2.g.text(a5)),
            Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc})),
            Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)), Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), zz), Lex.run(String.to_list(D2.g.text(a5)),
            Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc}), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc), lexg(a5, D2.GKVal{},
            M4.and_left(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})),
            M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc, ww, st)), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), M4.fl(gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)))}, Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, lexg(a7, D2.GKObj{},
            M4.and_right(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M4.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M4.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))))),
            acc, a6, gend(a5, Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc))(iw_gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc), M4.and_left(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))))), Equal.trans(Lex.Lex,
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), M4.fl(gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a5),
            V.WVal{}), Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc))}, Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, Equal.cong(List<&2, Lex.Tok>,
            Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), zz)},
            M4.fl(gend(a5, Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)), List.reverse.go(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc), fl_gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)), Equal.trans(Lex.Lex,
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), List.reverse.go(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            co(a7)), Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)}, Lex.Lex{Lex.Idle{}, [],
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, Equal.cong(List<&2, Lex.Tok>,
            Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> zz}, List.reverse.go(&2, Lex.Tok, co(a7),
            List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)), List.reverse.go(&2, Lex.Tok,
            List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}), co(a7)),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc), Equal.sym(List<&2, Lex.Tok>,
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}), co(a7)),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc), List.reverse.go(&2, Lex.Tok, co(a7),
            List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)), M12.rev_app(M12.tj_r(L2.g.val(a5),
            V.WVal{}), co(a7), Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc))),
            Equal.trans(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
            List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}), co(a7)),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TOpenObj{} <> acc)}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TOpenObj{} <> acc)}, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok,
            List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}, V.WObj{}),
            [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
            zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, zz, Lex.TOpenObj{} <> acc)},
            Lex.TStr{D2.spelled(a2)} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            co(a7)), M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}, V.WObj{}), Equal.sym(List<&2,
            Lex.Tok>, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}, V.WObj{}),
            Lex.TStr{D2.spelled(a2)} <> Lex.TColon{} <> List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            co(a7)), co_eq(D2.spelled(a2), L2.g.val(a5), a7, M4.and_right(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))))))), Equal.cong(List<&2,
            Lex.Tok>, Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [], zz}, Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}, V.WObj{}), Lex.TOpenObj{} <> acc),
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc), Equal.sym(List<&2, Lex.Tok>,
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc),
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TOpenObj{} <> acc), M10.rev_snoc_t(M12.tj_r(V.JPair{D2.spelled(a2),
            L2.g.val(a5), L2.g.val(a7)}, V.WObj{}), Lex.TCloseObj{}, Lex.TOpenObj{} <> acc)))))))))))))
        case D2.GKArr{}:
          M4.no(lgg(D2.GObj{a1, a2, a3, a4, a5, a6, a7}, D2.GKArr{}, acc, ww, st), h)
        case D2.GKObj{}:
          M4.no(lgg(D2.GObj{a1, a2, a3, a4, a5, a6, a7}, D2.GKObj{}, acc, ww, st), h)
    case D2.GEnd{}:
      match kk:
        case D2.GKVal{}:
          M4.no(lgg(D2.GEnd{}, D2.GKVal{}, acc, ww, st), h)
        case D2.GKArr{}:
          hi => hw => Equal.trans(Lex.Lex, Lex.run(String.to_list(ww ++ "]"), st), Lex.run(String.to_list("]"),
            Lex.run(String.to_list(ww), st)), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> M4.fl(st)}, M11.run_app(ww,
                "]", st),
            ws_punct(ww, ']', Lex.TCloseArr{}, {==}, st, hi, hw))
        case D2.GKObj{}:
          hi => hw => Equal.trans(Lex.Lex, Lex.run(String.to_list(ww ++ "}"), st), Lex.run(String.to_list("}"),
            Lex.run(String.to_list(ww), st)), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> M4.fl(st)}, M11.run_app(ww,
                "}", st),
            ws_punct(ww, '}', Lex.TCloseObj{}, {==}, st, hi, hw))
    case D2.GNext{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          M4.no(lgg(D2.GNext{a1, a2, a3, a4}, D2.GKVal{}, acc, ww, st), h)
        case D2.GKArr{}:
          hi => hw => Equal.trans(Lex.Lex,
            Lex.run(String.to_list(ww ++ ("," ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)) ++ "]"), st),
            Lex.run(String.to_list(("," ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)) ++ "]"),
            Lex.run(String.to_list(ww), st)), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, M11.run_app(ww,
            ("," ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)) ++ "]", st), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(("," ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)) ++ "]"),
            Lex.run(String.to_list(ww), st)), Lex.run(String.to_list("]"),
            Lex.run(String.to_list("," ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.run(String.to_list(ww),
            st))), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
                M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))},
            M11.run_app("," ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4), "]", Lex.run(String.to_list(ww), st)),
            Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
            Lex.run(String.to_list("," ++ a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.run(String.to_list(ww),
            st))), Lex.run(String.to_list("]"), Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)),
            Lex.feed(',', Lex.run(String.to_list(ww), st)))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}),
            Lex.TComma{} <> M4.fl(st))}, {==}, Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
            Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.feed(',',
            Lex.run(String.to_list(ww), st)))), Lex.run(String.to_list("]"),
            Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.Lex{Lex.Idle{}, [],
            Lex.TComma{} <> M4.fl(st)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex,
            Lex.Lex, zz => Lex.run(String.to_list("]"),
            Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), zz)), Lex.feed(',',
            Lex.run(String.to_list(ww), st)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}, ws_punct(ww, ',',
            Lex.TComma{}, {==}, st, hi, hw)), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
            Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.Lex{Lex.Idle{}, [],
            Lex.TComma{} <> M4.fl(st)})), Lex.run(String.to_list("]"),
            Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.run(String.to_list(a1),
            Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}),
            Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex, Lex.Lex, zz => Lex.run(String.to_list("]"), zz),
            Lex.run(String.to_list(a1 ++ D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.Lex{Lex.Idle{}, [],
            Lex.TComma{} <> M4.fl(st)}), Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4)),
            Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})), M11.run_app(a1,
            D2.g.text(a2) ++ a3 ++ D2.g.text(a4), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})),
            Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
            Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.run(String.to_list(a1),
            Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}))), Lex.run(String.to_list("]"),
            Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.Lex{Lex.Idle{}, [],
            Lex.TComma{} <> M4.fl(st)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex,
            Lex.Lex, zz => Lex.run(String.to_list("]"),
            Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), zz)), Lex.run(String.to_list(a1),
            Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)},
            ws_idle(a1, M4.and_left(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h), Lex.TComma{} <> M4.fl(st))), Equal.trans(Lex.Lex,
            Lex.run(String.to_list("]"), Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4)),
            Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})), Lex.run(String.to_list("]"),
            Lex.run(String.to_list(a3 ++ D2.g.text(a4)), Lex.run(String.to_list(D2.g.text(a2)), Lex.Lex{Lex.Idle{},
            [], Lex.TComma{} <> M4.fl(st)}))), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex,
            Lex.Lex, zz => Lex.run(String.to_list("]"), zz),
            Lex.run(String.to_list(D2.g.text(a2) ++ a3 ++ D2.g.text(a4)), Lex.Lex{Lex.Idle{}, [],
            Lex.TComma{} <> M4.fl(st)}), Lex.run(String.to_list(a3 ++ D2.g.text(a4)),
            Lex.run(String.to_list(D2.g.text(a2)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})),
            M11.run_app(D2.g.text(a2), a3 ++ D2.g.text(a4), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})),
            Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(a3 ++ D2.g.text(a4)),
            Lex.run(String.to_list(D2.g.text(a2)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}))),
            Lex.run(String.to_list("]"), Lex.run(String.to_list(a3 ++ D2.g.text(a4)), gend(a2,
            Lex.TComma{} <> M4.fl(st)))), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex,
            Lex.Lex, zz => Lex.run(String.to_list("]"), Lex.run(String.to_list(a3 ++ D2.g.text(a4)), zz)),
            Lex.run(String.to_list(D2.g.text(a2)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}), gend(a2,
            Lex.TComma{} <> M4.fl(st)), lexg(a2, D2.GKVal{}, M4.and_left(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h)), Lex.TComma{} <> M4.fl(st), ww,
            st)), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(a3 ++ D2.g.text(a4)),
            gend(a2, Lex.TComma{} <> M4.fl(st)))), Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"), gend(a2,
            Lex.TComma{} <> M4.fl(st))), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
            M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, Equal.sym(Lex.Lex,
            Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"), gend(a2, Lex.TComma{} <> M4.fl(st))),
            Lex.run(String.to_list("]"), Lex.run(String.to_list(a3 ++ D2.g.text(a4)), gend(a2,
            Lex.TComma{} <> M4.fl(st)))), run_assoc(a3, D2.g.text(a4), "]", gend(a2, Lex.TComma{} <> M4.fl(st)))),
            Equal.trans(Lex.Lex, Lex.run(String.to_list(a3 ++ D2.g.text(a4) ++ "]"), gend(a2,
            Lex.TComma{} <> M4.fl(st))), Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
                M12.ct(a4),
            M4.fl(gend(a2, Lex.TComma{} <> M4.fl(st))))}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2,
            Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, lexg(a4,
            D2.GKArr{}, M4.and_right(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h))), acc,
            a3, gend(a2, Lex.TComma{} <> M4.fl(st)))(iw_gend(a2, Lex.TComma{} <> M4.fl(st)), M4.and_left(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h)))), Equal.trans(Lex.Lex, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), M4.fl(gend(a2, Lex.TComma{} <> M4.fl(st))))},
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), List.reverse.go(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), Lex.TComma{} <> M4.fl(st)))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}),
            Lex.TComma{} <> M4.fl(st))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), zz)}, M4.fl(gend(a2,
                Lex.TComma{} <> M4.fl(st))),
            List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), Lex.TComma{} <> M4.fl(st)), fl_gend(a2,
            Lex.TComma{} <> M4.fl(st))), Equal.trans(Lex.Lex, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.ct(a4), List.reverse.go(&2, Lex.Tok,
                M12.tj_r(L2.g.val(a2),
            V.WVal{}), Lex.TComma{} <> M4.fl(st)))}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2,
            Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)),
                Lex.TComma{} <> M4.fl(st))},
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JCons{L2.g.val(a2),
            L2.g.val(a4)}, V.WArr{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
            zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> zz}, List.reverse.go(&2, Lex.Tok, M12.ct(a4),
            List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), Lex.TComma{} <> M4.fl(st))),
                List.reverse.go(&2,
            Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)), Lex.TComma{} <> M4.fl(st)),
            Equal.sym(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a2),
            V.WVal{}), M12.ct(a4)), Lex.TComma{} <> M4.fl(st)), List.reverse.go(&2, Lex.Tok, M12.ct(a4),
                List.reverse.go(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), Lex.TComma{} <> M4.fl(st))), M12.rev_app(M12.tj_r(L2.g.val(a2),
                V.WVal{}),
            M12.ct(a4), Lex.TComma{} <> M4.fl(st)))), Equal.cong(List<&2, Lex.Tok>, Lex.Lex, zz => Lex.Lex{Lex.Idle{},
                [],
            Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, zz, Lex.TComma{} <> M4.fl(st))}, List.append(&2, Lex.Tok,
            M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)), M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}),
            Equal.sym(List<&2, Lex.Tok>, M12.tj_r(V.JCons{L2.g.val(a2), L2.g.val(a4)}, V.WArr{}), List.append(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a2), V.WVal{}), M12.ct(a4)), ct_eq(L2.g.val(a2), a4, M4.and_right(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3),
            D2.g.ok(a4, D2.GKArr{}))), h))))))))))))))))))
        case D2.GKObj{}:
          M4.no(lgg(D2.GNext{a1, a2, a3, a4}, D2.GKObj{}, acc, ww, st), h)
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          M4.no(lgg(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}, D2.GKVal{}, acc, ww, st), h)
        case D2.GKArr{}:
          M4.no(lgg(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}, D2.GKArr{}, acc, ww, st), h)
        case D2.GKObj{}:
          hi => hw => Equal.trans(Lex.Lex,
            Lex.run(String.to_list(ww ++ ("," ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++
            D2.g.text(a5) ++ a6 ++ D2.g.text(a7)) ++ "}"), st),
            Lex.run(String.to_list(("," ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++
            D2.g.text(a5) ++ a6 ++ D2.g.text(a7)) ++ "}"), Lex.run(String.to_list(ww), st)), Lex.Lex{Lex.Idle{},
            [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, M11.run_app(ww,
            ("," ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)) ++ "}", st), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(("," ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++
            D2.g.text(a5) ++ a6 ++ D2.g.text(a7)) ++ "}"), Lex.run(String.to_list(ww), st)),
            Lex.run(String.to_list("}"),
            Lex.run(String.to_list("," ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++
            a6 ++ D2.g.text(a7)), Lex.run(String.to_list(ww), st))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))},
            M11.run_app("," ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7), "}", Lex.run(String.to_list(ww), st)), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
            Lex.run(String.to_list("," ++ a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++
            a6 ++ D2.g.text(a7)), Lex.run(String.to_list(ww), st))), Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.feed(',', Lex.run(String.to_list(ww), st)))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, {==}, Equal.trans(Lex.Lex,
            Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.feed(',', Lex.run(String.to_list(ww), st)))), Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), zz)), Lex.feed(',', Lex.run(String.to_list(ww), st)), Lex.Lex{Lex.Idle{}, [],
            Lex.TComma{} <> M4.fl(st)}, ws_punct(ww, ',', Lex.TComma{}, {==}, st, hi, hw)), Equal.trans(Lex.Lex,
            Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})), Lex.run(String.to_list("}"),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}))),
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2),
            L2.g.val(a5), L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list("}"), zz),
            Lex.run(String.to_list(a1 ++ "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})),
            M11.run_app(a1, "\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++ D2.g.text(a7),
            Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}))),
            Lex.run(String.to_list("}"),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list("}"),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), zz)), Lex.run(String.to_list(a1), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}),
            Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}, ws_idle(a1, M4.and_left(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h), Lex.TComma{} <> M4.fl(st))),
            Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)})), Lex.run(String.to_list("}"),
            Lex.run(String.to_list(D2.g.text(a5) ++ a6 ++ D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)})), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list("}"), zz),
            Lex.run(String.to_list("\"" ++ D2.spell(a2) ++ "\"" ++ a3 ++ ":" ++ a4 ++ D2.g.text(a5) ++ a6 ++
            D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> M4.fl(st)}),
            Lex.run(String.to_list(D2.g.text(a5) ++ a6 ++ D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)}), mem_in(a2, a3, a4,
            D2.g.text(a5) ++ a6 ++ D2.g.text(a7), M4.and_left(D2.spell_ok(a2), Bool.and(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))))), M4.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))))), h)), M4.and_left(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))), M4.and_left(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))),
            M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))), Lex.TComma{} <> M4.fl(st))),
            Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
            Lex.run(String.to_list(D2.g.text(a5) ++ a6 ++ D2.g.text(a7)), Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)})), Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a6 ++ D2.g.text(a7)), Lex.run(String.to_list(D2.g.text(a5)), Lex.Lex{Lex.Idle{},
            [], Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)}))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list("}"), zz), Lex.run(String.to_list(D2.g.text(a5) ++ a6 ++ D2.g.text(a7)),
            Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)}),
            Lex.run(String.to_list(a6 ++ D2.g.text(a7)), Lex.run(String.to_list(D2.g.text(a5)), Lex.Lex{Lex.Idle{},
            [], Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)})), M11.run_app(D2.g.text(a5),
            a6 ++ D2.g.text(a7), Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)})), Equal.trans(Lex.Lex,
            Lex.run(String.to_list("}"), Lex.run(String.to_list(a6 ++ D2.g.text(a7)),
            Lex.run(String.to_list(D2.g.text(a5)), Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)}))), Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a6 ++ D2.g.text(a7)), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(Lex.Lex, Lex.Lex,
            zz => Lex.run(String.to_list("}"), Lex.run(String.to_list(a6 ++ D2.g.text(a7)), zz)),
            Lex.run(String.to_list(D2.g.text(a5)), Lex.Lex{Lex.Idle{}, [],
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)}), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)), lexg(a5, D2.GKVal{},
            M4.and_left(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})),
            M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st), ww, st)), Equal.trans(Lex.Lex,
            Lex.run(String.to_list("}"), Lex.run(String.to_list(a6 ++ D2.g.text(a7)), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))),
            Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.sym(Lex.Lex,
            Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))), Lex.run(String.to_list("}"),
            Lex.run(String.to_list(a6 ++ D2.g.text(a7)), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))), run_assoc(a6, D2.g.text(a7),
            "}", gend(a5, Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))), Equal.trans(Lex.Lex,
            Lex.run(String.to_list(a6 ++ D2.g.text(a7) ++ "}"), gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))), Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), M4.fl(gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, lexg(a7, D2.GKObj{}, M4.and_right(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))))), acc, a6, gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))(iw_gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)), M4.and_left(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))))), Equal.trans(Lex.Lex,
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), M4.fl(gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a5),
            V.WVal{}), Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
            zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), zz)}, M4.fl(gend(a5,
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))), List.reverse.go(&2, Lex.Tok,
            M12.tj_r(L2.g.val(a5), V.WVal{}), Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)),
            fl_gend(a5, Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))), Equal.trans(Lex.Lex,
            Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, co(a7), List.reverse.go(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            co(a7)), Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))}, Lex.Lex{Lex.Idle{}, [],
            Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TComma{} <> M4.fl(st))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
            zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> zz}, List.reverse.go(&2, Lex.Tok, co(a7),
            List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))), List.reverse.go(&2, Lex.Tok,
            List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}), co(a7)),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)), Equal.sym(List<&2, Lex.Tok>,
            List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}), co(a7)),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)), List.reverse.go(&2, Lex.Tok, co(a7),
            List.reverse.go(&2, Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}),
            Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st))), M12.rev_app(M12.tj_r(L2.g.val(a5),
            V.WVal{}), co(a7), Lex.TColon{} <> Lex.TStr{D2.spelled(a2)} <> Lex.TComma{} <> M4.fl(st)))),
            Equal.cong(List<&2, Lex.Tok>, Lex.Lex, zz => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2,
            Lex.Tok, zz, Lex.TComma{} <> M4.fl(st))}, Lex.TStr{D2.spelled(a2)} <> Lex.TColon{} <> List.append(&2,
            Lex.Tok, M12.tj_r(L2.g.val(a5), V.WVal{}), co(a7)), M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Equal.sym(List<&2, Lex.Tok>, M12.tj_r(V.JPair{D2.spelled(a2), L2.g.val(a5),
            L2.g.val(a7)}, V.WObj{}), Lex.TStr{D2.spelled(a2)} <> Lex.TColon{} <> List.append(&2, Lex.Tok,
            M12.tj_r(L2.g.val(a5), V.WVal{}), co(a7)), co_eq(D2.spelled(a2), L2.g.val(a5), a7,
            M4.and_right(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M4.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M4.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))),
            h))))))))))))))))))))))

# laws/ParsesExactlyJsonTexts.bend: the value a derivation stands for

# the shape of what stands where a derivation stands
def shp(kk: D2.GK) -> V.Shape:
  match kk:
    case D2.GKVal{}:
      V.WVal{}
    case D2.GKArr{}:
      V.WArr{}
    case D2.GKObj{}:
      V.WObj{}

# a literal name or a number is a well-formed value
law wf_word.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +w: String
  for h: {Bool.or(b1, Bool.or(b2, Bool.or(b3, D1.number(String.to_list(w))))) == True{} : Bool}
  {V.wf.go(Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3,
    V.JBool{False{}}, V.JNum{w}))), V.WVal{}) == True{} : Bool}

def wf_word.at(b1, b2, b3, w, h):
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          match b3:
            case True{}:
              {==}
            case False{}:
              Equal.trans(Bool, V.num.ok(w), D1.number(String.to_list(w)), True{}, L1.num_grammar(w), h)

# a literal name's or a number's value is its canonical form
law canon_word.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +w: String
  {M9.canon_r(Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2, V.JBool{True{}}, Bool.pick(V.Json, b3,
    V.JBool{False{}}, V.JNum{w}))), V.WVal{}) == Bool.pick(V.Json, b1, V.JNull{}, Bool.pick(V.Json, b2,
    V.JBool{True{}}, Bool.pick(V.Json, b3, V.JBool{False{}}, V.JNum{w}))) : V.Json}

def canon_word.at(b1, b2, b3, _w):
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          match b3:
            case True{}:
              {==}
            case False{}:
              {==}

# the value a derivation stands for is well-formed
law gwf:
  for +gg: D2.Gv
  for kk: D2.GK
  for +h: {D2.g.ok(gg, kk) == True{} : Bool}
  {V.wf.go(L2.g.val(gg), shp(kk)) == True{} : Bool}

def gwf(gg, kk, h):
  match gg:
    case D2.GWord{+a1}:
      match kk:
        case D2.GKVal{}:
          wf_word.at(String.eq(a1, "null"), String.eq(a1, "true"), String.eq(a1, "false"), a1, h)
        case D2.GKArr{}:
          M4.no({V.wf.go(L2.g.val(D2.GWord{a1}), shp(D2.GKArr{})) == True{} : Bool}, h)
        case D2.GKObj{}:
          M4.no({V.wf.go(L2.g.val(D2.GWord{a1}), shp(D2.GKObj{})) == True{} : Bool}, h)
    case D2.GStr{+a1}:
      match kk:
        case D2.GKVal{}:
          {==}
        case D2.GKArr{}:
          M4.no({V.wf.go(L2.g.val(D2.GStr{a1}), shp(D2.GKArr{})) == True{} : Bool}, h)
        case D2.GKObj{}:
          M4.no({V.wf.go(L2.g.val(D2.GStr{a1}), shp(D2.GKObj{})) == True{} : Bool}, h)
    case D2.GArr0{+a1}:
      match kk:
        case D2.GKVal{}:
          {==}
        case D2.GKArr{}:
          M4.no({V.wf.go(L2.g.val(D2.GArr0{a1}), shp(D2.GKArr{})) == True{} : Bool}, h)
        case D2.GKObj{}:
          M4.no({V.wf.go(L2.g.val(D2.GArr0{a1}), shp(D2.GKObj{})) == True{} : Bool}, h)
    case D2.GArr{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          M12.cons_wf(L2.g.val(a2), L2.g.val(a4), gwf(a2, D2.GKVal{}, M4.and_left(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h))), gwf(a4, D2.GKArr{},
            M4.and_right(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h)))))
        case D2.GKArr{}:
          M4.no({V.wf.go(L2.g.val(D2.GArr{a1, a2, a3, a4}), shp(D2.GKArr{})) == True{} : Bool}, h)
        case D2.GKObj{}:
          M4.no({V.wf.go(L2.g.val(D2.GArr{a1, a2, a3, a4}), shp(D2.GKObj{})) == True{} : Bool}, h)
    case D2.GObj0{+a1}:
      match kk:
        case D2.GKVal{}:
          {==}
        case D2.GKArr{}:
          M4.no({V.wf.go(L2.g.val(D2.GObj0{a1}), shp(D2.GKArr{})) == True{} : Bool}, h)
        case D2.GKObj{}:
          M4.no({V.wf.go(L2.g.val(D2.GObj0{a1}), shp(D2.GKObj{})) == True{} : Bool}, h)
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          M12.pair_wf(Parse.KOwn{D2.spelled(a2)}, L2.g.val(a5), L2.g.val(a7), gwf(a5, D2.GKVal{},
            M4.and_left(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})),
            M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))))), gwf(a7, D2.GKObj{},
            M4.and_right(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M4.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M4.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))))))
        case D2.GKArr{}:
          M4.no({V.wf.go(L2.g.val(D2.GObj{a1, a2, a3, a4, a5, a6, a7}), shp(D2.GKArr{})) == True{} : Bool}, h)
        case D2.GKObj{}:
          M4.no({V.wf.go(L2.g.val(D2.GObj{a1, a2, a3, a4, a5, a6, a7}), shp(D2.GKObj{})) == True{} : Bool}, h)
    case D2.GEnd{}:
      match kk:
        case D2.GKVal{}:
          M4.no({V.wf.go(L2.g.val(D2.GEnd{}), shp(D2.GKVal{})) == True{} : Bool}, h)
        case D2.GKArr{}:
          {==}
        case D2.GKObj{}:
          {==}
    case D2.GNext{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          M4.no({V.wf.go(L2.g.val(D2.GNext{a1, a2, a3, a4}), shp(D2.GKVal{})) == True{} : Bool}, h)
        case D2.GKArr{}:
          M12.cons_wf(L2.g.val(a2), L2.g.val(a4), gwf(a2, D2.GKVal{}, M4.and_left(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h))), gwf(a4, D2.GKArr{},
            M4.and_right(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h)))))
        case D2.GKObj{}:
          M4.no({V.wf.go(L2.g.val(D2.GNext{a1, a2, a3, a4}), shp(D2.GKObj{})) == True{} : Bool}, h)
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          M4.no({V.wf.go(L2.g.val(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}), shp(D2.GKVal{})) == True{} : Bool}, h)
        case D2.GKArr{}:
          M4.no({V.wf.go(L2.g.val(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}), shp(D2.GKArr{})) == True{} : Bool}, h)
        case D2.GKObj{}:
          M12.pair_wf(Parse.KOwn{D2.spelled(a2)}, L2.g.val(a5), L2.g.val(a7), gwf(a5, D2.GKVal{},
            M4.and_left(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})),
            M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))))), gwf(a7, D2.GKObj{},
            M4.and_right(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M4.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M4.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))))))

# the value a derivation stands for is its own canonical form
law canon_g:
  for +gg: D2.Gv
  for kk: D2.GK
  for +h: {D2.g.ok(gg, kk) == True{} : Bool}
  {M9.canon_r(L2.g.val(gg), shp(kk)) == L2.g.val(gg) : V.Json}

def canon_g(gg, kk, h):
  match gg:
    case D2.GWord{+a1}:
      match kk:
        case D2.GKVal{}:
          canon_word.at(String.eq(a1, "null"), String.eq(a1, "true"), String.eq(a1, "false"), a1)
        case D2.GKArr{}:
          M4.no({M9.canon_r(L2.g.val(D2.GWord{a1}), shp(D2.GKArr{})) == L2.g.val(D2.GWord{a1}) : V.Json}, h)
        case D2.GKObj{}:
          M4.no({M9.canon_r(L2.g.val(D2.GWord{a1}), shp(D2.GKObj{})) == L2.g.val(D2.GWord{a1}) : V.Json}, h)
    case D2.GStr{+a1}:
      match kk:
        case D2.GKVal{}:
          {==}
        case D2.GKArr{}:
          M4.no({M9.canon_r(L2.g.val(D2.GStr{a1}), shp(D2.GKArr{})) == L2.g.val(D2.GStr{a1}) : V.Json}, h)
        case D2.GKObj{}:
          M4.no({M9.canon_r(L2.g.val(D2.GStr{a1}), shp(D2.GKObj{})) == L2.g.val(D2.GStr{a1}) : V.Json}, h)
    case D2.GArr0{+a1}:
      match kk:
        case D2.GKVal{}:
          {==}
        case D2.GKArr{}:
          M4.no({M9.canon_r(L2.g.val(D2.GArr0{a1}), shp(D2.GKArr{})) == L2.g.val(D2.GArr0{a1}) : V.Json}, h)
        case D2.GKObj{}:
          M4.no({M9.canon_r(L2.g.val(D2.GArr0{a1}), shp(D2.GKObj{})) == L2.g.val(D2.GArr0{a1}) : V.Json}, h)
    case D2.GArr{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          Equal.trans(V.Json, V.JArr{V.JCons{M9.canon_r(L2.g.val(a2), V.WVal{}), M9.canon_r(L2.g.val(a4), V.WArr{})}},
            V.JArr{V.JCons{L2.g.val(a2), M9.canon_r(L2.g.val(a4), V.WArr{})}}, V.JArr{V.JCons{L2.g.val(a2),
            L2.g.val(a4)}}, Equal.cong(V.Json, V.Json, zz => V.JArr{V.JCons{zz, M9.canon_r(L2.g.val(a4), V.WArr{})}},
            M9.canon_r(L2.g.val(a2), V.WVal{}), L2.g.val(a2), canon_g(a2, D2.GKVal{}, M4.and_left(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h)))),
            Equal.cong(V.Json, V.Json, zz => V.JArr{V.JCons{L2.g.val(a2), zz}}, M9.canon_r(L2.g.val(a4), V.WArr{}),
            L2.g.val(a4), canon_g(a4, D2.GKArr{}, M4.and_right(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}),
            M4.and_right(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})),
            M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4,
            D2.GKArr{}))), h))))))
        case D2.GKArr{}:
          M4.no({M9.canon_r(L2.g.val(D2.GArr{a1, a2, a3, a4}), shp(D2.GKArr{})) == L2.g.val(D2.GArr{a1, a2, a3,
            a4}) : V.Json}, h)
        case D2.GKObj{}:
          M4.no({M9.canon_r(L2.g.val(D2.GArr{a1, a2, a3, a4}), shp(D2.GKObj{})) == L2.g.val(D2.GArr{a1, a2, a3,
            a4}) : V.Json}, h)
    case D2.GObj0{+a1}:
      match kk:
        case D2.GKVal{}:
          {==}
        case D2.GKArr{}:
          M4.no({M9.canon_r(L2.g.val(D2.GObj0{a1}), shp(D2.GKArr{})) == L2.g.val(D2.GObj0{a1}) : V.Json}, h)
        case D2.GKObj{}:
          M4.no({M9.canon_r(L2.g.val(D2.GObj0{a1}), shp(D2.GKObj{})) == L2.g.val(D2.GObj0{a1}) : V.Json}, h)
    case D2.GObj{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          Equal.trans(V.Json, V.JObj{V.JPair{D2.spelled(a2), M9.canon_r(L2.g.val(a5), V.WVal{}),
            M9.canon_r(L2.g.val(a7), V.WObj{})}}, V.JObj{V.JPair{D2.spelled(a2), L2.g.val(a5),
            M9.canon_r(L2.g.val(a7), V.WObj{})}}, V.JObj{V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}},
            Equal.cong(V.Json, V.Json, zz => V.JObj{V.JPair{D2.spelled(a2), zz, M9.canon_r(L2.g.val(a7), V.WObj{})}},
            M9.canon_r(L2.g.val(a5), V.WVal{}), L2.g.val(a5), canon_g(a5, D2.GKVal{}, M4.and_left(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})), M4.and_right(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))),
            M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))))), Equal.cong(V.Json,
            V.Json, zz => V.JObj{V.JPair{D2.spelled(a2), L2.g.val(a5), zz}}, M9.canon_r(L2.g.val(a7), V.WObj{}),
            L2.g.val(a7), canon_g(a7, D2.GKObj{}, M4.and_right(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}),
            M4.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})),
            M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))))))))
        case D2.GKArr{}:
          M4.no({M9.canon_r(L2.g.val(D2.GObj{a1, a2, a3, a4, a5, a6, a7}), shp(D2.GKArr{})) == L2.g.val(D2.GObj{a1,
            a2, a3, a4, a5, a6, a7}) : V.Json}, h)
        case D2.GKObj{}:
          M4.no({M9.canon_r(L2.g.val(D2.GObj{a1, a2, a3, a4, a5, a6, a7}), shp(D2.GKObj{})) == L2.g.val(D2.GObj{a1,
            a2, a3, a4, a5, a6, a7}) : V.Json}, h)
    case D2.GEnd{}:
      match kk:
        case D2.GKVal{}:
          M4.no({M9.canon_r(L2.g.val(D2.GEnd{}), shp(D2.GKVal{})) == L2.g.val(D2.GEnd{}) : V.Json}, h)
        case D2.GKArr{}:
          {==}
        case D2.GKObj{}:
          {==}
    case D2.GNext{+a1, +a2, +a3, +a4}:
      match kk:
        case D2.GKVal{}:
          M4.no({M9.canon_r(L2.g.val(D2.GNext{a1, a2, a3, a4}), shp(D2.GKVal{})) == L2.g.val(D2.GNext{a1, a2, a3,
            a4}) : V.Json}, h)
        case D2.GKArr{}:
          Equal.trans(V.Json, V.JCons{M9.canon_r(L2.g.val(a2), V.WVal{}), M9.canon_r(L2.g.val(a4), V.WArr{})},
            V.JCons{L2.g.val(a2), M9.canon_r(L2.g.val(a4), V.WArr{})}, V.JCons{L2.g.val(a2), L2.g.val(a4)},
            Equal.cong(V.Json, V.Json, zz => V.JCons{zz, M9.canon_r(L2.g.val(a4), V.WArr{})}, M9.canon_r(L2.g.val(a2),
            V.WVal{}), L2.g.val(a2), canon_g(a2, D2.GKVal{}, M4.and_left(D2.g.ok(a2, D2.GKVal{}),
            Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1), Bool.and(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h)))), Equal.cong(V.Json, V.Json,
            zz => V.JCons{L2.g.val(a2), zz}, M9.canon_r(L2.g.val(a4), V.WArr{}), L2.g.val(a4), canon_g(a4,
            D2.GKArr{}, M4.and_right(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}), M4.and_right(D2.g.ok(a2,
            D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{})), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.g.ok(a2, D2.GKVal{}), Bool.and(D1.all_ws(a3), D2.g.ok(a4, D2.GKArr{}))), h))))))
        case D2.GKObj{}:
          M4.no({M9.canon_r(L2.g.val(D2.GNext{a1, a2, a3, a4}), shp(D2.GKObj{})) == L2.g.val(D2.GNext{a1, a2, a3,
            a4}) : V.Json}, h)
    case D2.GNextM{+a1, +a2, +a3, +a4, +a5, +a6, +a7}:
      match kk:
        case D2.GKVal{}:
          M4.no({M9.canon_r(L2.g.val(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}),
            shp(D2.GKVal{})) == L2.g.val(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}) : V.Json}, h)
        case D2.GKArr{}:
          M4.no({M9.canon_r(L2.g.val(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}),
            shp(D2.GKArr{})) == L2.g.val(D2.GNextM{a1, a2, a3, a4, a5, a6, a7}) : V.Json}, h)
        case D2.GKObj{}:
          Equal.trans(V.Json, V.JPair{D2.spelled(a2), M9.canon_r(L2.g.val(a5), V.WVal{}), M9.canon_r(L2.g.val(a7),
            V.WObj{})}, V.JPair{D2.spelled(a2), L2.g.val(a5), M9.canon_r(L2.g.val(a7), V.WObj{})},
            V.JPair{D2.spelled(a2), L2.g.val(a5), L2.g.val(a7)}, Equal.cong(V.Json, V.Json,
            zz => V.JPair{D2.spelled(a2), zz, M9.canon_r(L2.g.val(a7), V.WObj{})}, M9.canon_r(L2.g.val(a5), V.WVal{}),
            L2.g.val(a5), canon_g(a5, D2.GKVal{}, M4.and_left(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3),
            Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})))), M4.and_right(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))),
            M4.and_right(D1.all_ws(a1), Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4),
            Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h))))))),
            Equal.cong(V.Json, V.Json, zz => V.JPair{D2.spelled(a2), L2.g.val(a5), zz}, M9.canon_r(L2.g.val(a7),
            V.WObj{}), L2.g.val(a7), canon_g(a7, D2.GKObj{}, M4.and_right(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{}), M4.and_right(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7,
            D2.GKObj{})), M4.and_right(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}), Bool.and(D1.all_ws(a6),
            D2.g.ok(a7, D2.GKObj{}))), M4.and_right(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))), M4.and_right(D2.spell_ok(a2),
            Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5, D2.GKVal{}),
            Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{}))))), M4.and_right(D1.all_ws(a1),
            Bool.and(D2.spell_ok(a2), Bool.and(D1.all_ws(a3), Bool.and(D1.all_ws(a4), Bool.and(D2.g.ok(a5,
            D2.GKVal{}), Bool.and(D1.all_ws(a6), D2.g.ok(a7, D2.GKObj{})))))), h)))))))))

# laws/ParsesExactlyJsonTexts.bend: a derived text parses

# a derived text, whitespace around a value, read by the character lexer, is
# the value's tokens
law lex_text:
  for +gg: D2.Gv
  for +wa: String
  for +wb: String
  for +h_g: {D2.g.ok(gg, D2.GKVal{}) == True{} : Bool}
  for +h_a: {D1.all_ws(wa) == True{} : Bool}
  for +h_b: {D1.all_ws(wb) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list(wa ++ D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [],
    []})) == M12.tj_r(L2.g.val(gg), V.WVal{}) : List<&2, Lex.Tok>}

def lex_text(gg, wa, wb, h_g, h_a, h_b):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(wa ++ D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{},
    [], []})), Lex.finish(Lex.run(String.to_list(D2.g.text(gg) ++ wb), Lex.run(String.to_list(wa),
    Lex.Lex{Lex.Idle{}, [], []}))), M12.tj_r(L2.g.val(gg), V.WVal{}), Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
    zz => Lex.finish(zz), Lex.run(String.to_list(wa ++ D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [], []}),
    Lex.run(String.to_list(D2.g.text(gg) ++ wb), Lex.run(String.to_list(wa), Lex.Lex{Lex.Idle{}, [], []})),
    M11.run_app(wa, D2.g.text(gg) ++ wb, Lex.Lex{Lex.Idle{}, [], []})), Equal.trans(List<&2, Lex.Tok>,
    Lex.finish(Lex.run(String.to_list(D2.g.text(gg) ++ wb), Lex.run(String.to_list(wa), Lex.Lex{Lex.Idle{}, [],
    []}))), Lex.finish(Lex.run(String.to_list(D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [], []})),
    M12.tj_r(L2.g.val(gg), V.WVal{}), Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
    zz => Lex.finish(Lex.run(String.to_list(D2.g.text(gg) ++ wb), zz)), Lex.run(String.to_list(wa),
    Lex.Lex{Lex.Idle{}, [], []}), Lex.Lex{Lex.Idle{}, [], []}, ws_idle(wa, h_a, [])), Equal.trans(List<&2, Lex.Tok>,
    Lex.finish(Lex.run(String.to_list(D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [], []})),
    Lex.finish(Lex.run(String.to_list(wb), Lex.run(String.to_list(D2.g.text(gg)), Lex.Lex{Lex.Idle{}, [], []}))),
    M12.tj_r(L2.g.val(gg), V.WVal{}), Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz),
    Lex.run(String.to_list(D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [], []}), Lex.run(String.to_list(wb),
    Lex.run(String.to_list(D2.g.text(gg)), Lex.Lex{Lex.Idle{}, [], []})), M11.run_app(D2.g.text(gg), wb,
    Lex.Lex{Lex.Idle{}, [], []})), Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(wb),
    Lex.run(String.to_list(D2.g.text(gg)), Lex.Lex{Lex.Idle{}, [], []}))), Lex.finish(Lex.run(String.to_list(wb),
    gend(gg, []))), M12.tj_r(L2.g.val(gg), V.WVal{}), Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
    zz => Lex.finish(Lex.run(String.to_list(wb), zz)), Lex.run(String.to_list(D2.g.text(gg)), Lex.Lex{Lex.Idle{}, [],
    []}), gend(gg, []), lexg(gg, D2.GKVal{}, h_g, [], wb, Lex.Lex{Lex.Idle{}, [], []})), Equal.trans(List<&2,
    Lex.Tok>, Lex.finish(Lex.run(String.to_list(wb), gend(gg, []))), List.reverse(&2, Lex.Tok, M4.fl(gend(gg, []))),
    M12.tj_r(L2.g.val(gg), V.WVal{}), ws_fin(wb, gend(gg, []), iw_gend(gg, []), h_b), Equal.trans(List<&2, Lex.Tok>,
    List.reverse(&2, Lex.Tok, M4.fl(gend(gg, []))), List.reverse(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok,
    M12.tj_r(L2.g.val(gg), V.WVal{}), [])), M12.tj_r(L2.g.val(gg), V.WVal{}), Equal.cong(List<&2, Lex.Tok>, List<&2,
    Lex.Tok>, zz => List.reverse(&2, Lex.Tok, zz), M4.fl(gend(gg, [])), List.reverse.go(&2, Lex.Tok,
        M12.tj_r(L2.g.val(gg),
    V.WVal{}), []), fl_gend(gg, [])), Equal.trans(List<&2, Lex.Tok>, List.reverse(&2, Lex.Tok, List.reverse.go(&2,
    Lex.Tok, M12.tj_r(L2.g.val(gg), V.WVal{}), [])), List.append(&2, Lex.Tok, M12.tj_r(L2.g.val(gg), V.WVal{}), []),
    M12.tj_r(L2.g.val(gg), V.WVal{}), M3.rev_rev(M12.tj_r(L2.g.val(gg), V.WVal{}), [], []),
        M3.lapp_nil(M12.tj_r(L2.g.val(gg),
    V.WVal{})))))))))

def L2.text_some(gg, wa, wb, h_g, h_a, h_b, h_s):
  Equal.trans(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens(wa ++ D2.g.text(gg) ++ wb),
    Parse.P{False{}, None{}, Nil{}}))), Parse.finish(M8.ownp(Parse.run(Lex.tokens(wa ++ D2.g.text(gg) ++ wb),
    Parse.P{False{}, None{}, Nil{}}))), Some{L2.g.val(gg)},
    M8.fin_own(Parse.run(Lex.tokens(wa ++ D2.g.text(gg) ++ wb), Parse.P{False{}, None{}, Nil{}})), Equal.trans(Maybe<&2,
    V.Json>, Parse.finish(M8.ownp(Parse.run(Lex.tokens(wa ++ D2.g.text(gg) ++ wb), Parse.P{False{}, None{}, Nil{}}))),
    Parse.finish(Parse.run(M4.dens(Lex.tokens(wa ++ D2.g.text(gg) ++ wb)), Parse.P{False{}, None{}, Nil{}})),
    Some{L2.g.val(gg)}, Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz),
    M8.ownp(Parse.run(Lex.tokens(wa ++ D2.g.text(gg) ++ wb), Parse.P{False{}, None{}, Nil{}})),
    Parse.run(M4.dens(Lex.tokens(wa ++ D2.g.text(gg) ++ wb)), Parse.P{False{}, None{}, Nil{}}),
    M8.run_own(Lex.tokens(wa ++ D2.g.text(gg) ++ wb), Parse.P{False{}, None{}, Nil{}})), Equal.trans(Maybe<&2, V.Json>,
    Parse.finish(Parse.run(M4.dens(Lex.tokens(wa ++ D2.g.text(gg) ++ wb)), Parse.P{False{}, None{}, Nil{}})),
    Parse.finish(Parse.run(M12.tj_r(L2.g.val(gg), V.WVal{}), Parse.P{False{}, None{}, Nil{}})), Some{L2.g.val(gg)},
    Equal.cong(List<&2, Lex.Tok>, Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(zz, Parse.P{False{}, None{},
    Nil{}})), M4.dens(Lex.tokens(wa ++ D2.g.text(gg) ++ wb)), M12.tj_r(L2.g.val(gg), V.WVal{}), Equal.trans(List<&2,
    Lex.Tok>, M4.dens(Lex.tokens(wa ++ D2.g.text(gg) ++ wb)),
    M4.dens(Lex.finish(Lex.run(String.to_list(wa ++ D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [], []}))),
    M12.tj_r(L2.g.val(gg), V.WVal{}), M2.lexers_agree(wa ++ D2.g.text(gg) ++ wb, h_s), Equal.trans(List<&2, Lex.Tok>,
    M4.dens(Lex.finish(Lex.run(String.to_list(wa ++ D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [], []}))),
    M4.dens(M12.tj_r(L2.g.val(gg), V.WVal{})), M12.tj_r(L2.g.val(gg), V.WVal{}), Equal.cong(List<&2, Lex.Tok>, List<&2,
    Lex.Tok>, zz => M4.dens(zz), Lex.finish(Lex.run(String.to_list(wa ++ D2.g.text(gg) ++ wb), Lex.Lex{Lex.Idle{}, [],
    []})), M12.tj_r(L2.g.val(gg), V.WVal{}), lex_text(gg, wa, wb, h_g, h_a, h_b)), M3.dens_tjr(L2.g.val(gg),
        V.WVal{})))),
    Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M12.tj_r(L2.g.val(gg), V.WVal{}), Parse.P{False{}, None{},
    Nil{}})), Some{M9.canon_r(L2.g.val(gg), V.WVal{})}, Some{L2.g.val(gg)}, parse_tjr(L2.g.val(gg), gwf(gg,
    D2.GKVal{}, h_g)), Equal.cong(V.Json, Maybe<&2, V.Json>, zz => Some{zz}, M9.canon_r(L2.g.val(gg), V.WVal{}),
    L2.g.val(gg), canon_g(gg, D2.GKVal{}, h_g))))))

# appending strings is associative
law sassoc:
  for +aa: String
  for +bb: String
  for +cc: String
  {(aa ++ bb) ++ cc == aa ++ (bb ++ cc) : String}

def sassoc(aa, bb, cc):
  match aa:
    case SNil{}:
      {==}
    case SCon{hd, tl}:
      Equal.cong(String, String, xx => SCon{hd, xx}, (tl ++ bb) ++ cc, tl ++ (bb ++ cc), sassoc(tl, bb, cc))

# where the cursor is after a value that landed on `stack`, with `tail` left
def aft.on(tail: String, spot: Pull.Spot) -> Pull.Cur:
  match spot:
    case Pull.Spot{st, root}:
      Pull.Cur{tail, st, root, False{}}
    case Pull.SpotBad{}:
      Pull.Cur{"", [], False{}, True{}}

# where the cursor is after a value in the slot `stack` gives it
def aft(tail: String, stack: List<&2, Pull.Frame>) -> Pull.Cur:
  aft.on(tail, Pull.place.spot(stack))

# a code point none of the delimiter tests hold of is no delimiter
law spec_false.go:
  for +uu: U32
  for e9: {U32.is_eq(uu, 9) == False{} : Bool}
  for e10: {U32.is_eq(uu, 10) == False{} : Bool}
  for e13: {U32.is_eq(uu, 13) == False{} : Bool}
  for e32: {U32.is_eq(uu, 32) == False{} : Bool}
  for e34: {U32.is_eq(uu, 34) == False{} : Bool}
  for e44: {U32.is_eq(uu, 44) == False{} : Bool}
  for e58: {U32.is_eq(uu, 58) == False{} : Bool}
  for e91: {U32.is_eq(uu, 91) == False{} : Bool}
  for e92: {U32.is_eq(uu, 92) == False{} : Bool}
  for e93: {U32.is_eq(uu, 93) == False{} : Bool}
  for e123: {U32.is_eq(uu, 123) == False{} : Bool}
  for e125: {U32.is_eq(uu, 125) == False{} : Bool}
  {Pull.word.special(uu) == False{} : Bool}

def spec_false.go(uu, e9, e10, e13, e32, e34, e44, e58, e91, e92, e93, e123, e125):
  s9 = Equal.sym(Bool, U32.is_eq(uu, 9), False{}, e9)
  s10 = Equal.sym(Bool, U32.is_eq(uu, 10), False{}, e10)
  s13 = Equal.sym(Bool, U32.is_eq(uu, 13), False{}, e13)
  s32 = Equal.sym(Bool, U32.is_eq(uu, 32), False{}, e32)
  s34 = Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34)
  s44 = Equal.sym(Bool, U32.is_eq(uu, 44), False{}, e44)
  s58 = Equal.sym(Bool, U32.is_eq(uu, 58), False{}, e58)
  s91 = Equal.sym(Bool, U32.is_eq(uu, 91), False{}, e91)
  s92 = Equal.sym(Bool, U32.is_eq(uu, 92), False{}, e92)
  s93 = Equal.sym(Bool, U32.is_eq(uu, 93), False{}, e93)
  s123 = Equal.sym(Bool, U32.is_eq(uu, 123), False{}, e123)
  s125 = Equal.sym(Bool, U32.is_eq(uu, 125), False{}, e125)
  %s9 : {Bool.or(_, Bool.or(U32.is_eq(uu, 10), Bool.or(U32.is_eq(uu, 13), Bool.or(U32.is_eq(uu, 32),
    Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 44), Bool.or(U32.is_eq(uu, 58), Bool.or(U32.is_eq(uu, 91),
    Bool.or(U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 93), Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu,
    125)))))))))))) == False{} : Bool}
  %s10 : {Bool.or(_, Bool.or(U32.is_eq(uu, 13), Bool.or(U32.is_eq(uu, 32), Bool.or(U32.is_eq(uu, 34),
    Bool.or(U32.is_eq(uu, 44), Bool.or(U32.is_eq(uu, 58), Bool.or(U32.is_eq(uu, 91), Bool.or(U32.is_eq(uu, 92),
    Bool.or(U32.is_eq(uu, 93), Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu, 125))))))))))) == False{} : Bool}
  %s13 : {Bool.or(_, Bool.or(U32.is_eq(uu, 32), Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 44),
    Bool.or(U32.is_eq(uu, 58), Bool.or(U32.is_eq(uu, 91), Bool.or(U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 93),
    Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu, 125)))))))))) == False{} : Bool}
  %s32 : {Bool.or(_, Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 44), Bool.or(U32.is_eq(uu, 58),
    Bool.or(U32.is_eq(uu, 91), Bool.or(U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 93), Bool.or(U32.is_eq(uu, 123),
    U32.is_eq(uu, 125))))))))) == False{} : Bool}
  %s34 : {Bool.or(_, Bool.or(U32.is_eq(uu, 44), Bool.or(U32.is_eq(uu, 58), Bool.or(U32.is_eq(uu, 91),
    Bool.or(U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 93), Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu,
    125)))))))) == False{} : Bool}
  %s44 : {Bool.or(_, Bool.or(U32.is_eq(uu, 58), Bool.or(U32.is_eq(uu, 91), Bool.or(U32.is_eq(uu, 92),
    Bool.or(U32.is_eq(uu, 93), Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu, 125))))))) == False{} : Bool}
  %s58 : {Bool.or(_, Bool.or(U32.is_eq(uu, 91), Bool.or(U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 93),
    Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu, 125)))))) == False{} : Bool}
  %s91 : {Bool.or(_, Bool.or(U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 93), Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu,
    125))))) == False{} : Bool}
  %s92 : {Bool.or(_, Bool.or(U32.is_eq(uu, 93), Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu, 125)))) == False{} : Bool}
  %s93 : {Bool.or(_, Bool.or(U32.is_eq(uu, 123), U32.is_eq(uu, 125))) == False{} : Bool}
  %s123 : {Bool.or(_, U32.is_eq(uu, 125)) == False{} : Bool}
  %s125 : {_ == False{} : Bool}
  {==}

# a word character is no delimiter
law spec_false:
  for +ch: Char
  for +hc: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  {Pull.word.special(Char.to_u32(ch)) == False{} : Bool}

def spec_false(ch, hc):
  match ch:
    case Chr{+uu}:
      spec_false.go(uu, M12.neq_cls(U32.is_eq(uu, 9), uu, 9, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 10), uu, 10, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 13), uu, 13, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 32), uu, 32, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 34), uu, 34, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 44), uu, 44, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 58), uu, 58, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 91), uu, 91, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 92), uu, 92, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 93), uu, 93, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 123), uu, 123, {==}, hc, {==}),
        M12.neq_cls(U32.is_eq(uu, 125), uu, 125, {==}, hc, {==}))

# a character that is not a word character is a delimiter, once the test is named
law spec_true.at:
  for +ch: Char
  for bs: Bool
  for es: {Pull.word.special(Char.to_u32(ch)) == bs : Bool}
  for hn: {M4.is_other(Lex.classify(ch)) == False{} : Bool}
  {Pull.word.special(Char.to_u32(ch)) == True{} : Bool}

def spec_true.at(ch, bs, es, hn):
  match bs:
    case True{}:
      es
    case False{}:
      hc = M14.cls_by(ch, xx => Bool.not(Pull.word.special(xx)),
        Equal.cong(Bool, Bool, xx => Bool.not(xx), Pull.word.special(Char.to_u32(ch)), False{}, es),
        {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
      Empty.absurd({Pull.word.special(Char.to_u32(ch)) == True{} : Bool}, M1.true_false(Equal.trans(Bool, True{},
        M4.is_other(Lex.classify(ch)), False{}, Equal.cong(Lex.Class, Bool, xx => M4.is_other(xx), Lex.COther{},
          Lex.classify(ch), Equal.sym(Lex.Class, Lex.classify(ch), Lex.COther{}, hc)), hn)))

# a character that is not a word character is a delimiter
law spec_true:
  for +ch: Char
  for hn: {M4.is_other(Lex.classify(ch)) == False{} : Bool}
  {Pull.word.special(Char.to_u32(ch)) == True{} : Bool}

def spec_true(ch, hn):
  spec_true.at(ch, Pull.word.special(Char.to_u32(ch)), {==}, hn)

# a character that is not a word character is no digit, once the test is named
law dig_false.at:
  for +ch: Char
  for bd: Bool
  for ed: {V.num.ok.digit(Char.to_u32(ch)) == bd : Bool}
  for hn: {M4.is_other(Lex.classify(ch)) == False{} : Bool}
  {V.num.ok.digit(Char.to_u32(ch)) == False{} : Bool}

def dig_false.at(ch, bd, ed, hn):
  match bd:
    case False{}:
      ed
    case True{}:
      hc = M6.oth_digit(ch, ed)
      Empty.absurd({V.num.ok.digit(Char.to_u32(ch)) == False{} : Bool}, M1.true_false(Equal.trans(Bool, True{},
        M4.is_other(Lex.classify(ch)), False{}, Equal.cong(Lex.Class, Bool, xx => M4.is_other(xx), Lex.COther{},
          Lex.classify(ch), Equal.sym(Lex.Class, Lex.classify(ch), Lex.COther{}, hc)), hn)))

# a character that is not a word character is no digit
law dig_false:
  for +ch: Char
  for hn: {M4.is_other(Lex.classify(ch)) == False{} : Bool}
  {V.num.ok.digit(Char.to_u32(ch)) == False{} : Bool}

def dig_false(ch, hn):
  dig_false.at(ch, V.num.ok.digit(Char.to_u32(ch)), {==}, hn)

# a word character grows the word, once the digit test is named
law decide_oth.at:
  for +ch: Char
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for bd: Bool
  for ed: {V.num.ok.digit(Char.to_u32(ch)) == bd : Bool}
  for hc: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  {Pull.word.decide(ch, Char.to_u32(ch), buf, nn, num)
    == Pull.WMore{ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch))} : Pull.Wst}

def decide_oth.at(ch, buf, nn, num, bd, ed, hc):
  match bd:
    case True{}:
      es = Equal.sym(Bool, V.num.ok.digit(Char.to_u32(ch)), True{}, ed)
      %es : {Pull.word.digit.go(ch, Char.to_u32(ch), buf, nn, num, _)
        == Pull.WMore{ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch))} : Pull.Wst}
      {==}
    case False{}:
      es = Equal.sym(Bool, V.num.ok.digit(Char.to_u32(ch)), False{}, ed)
      %es : {Pull.word.digit.go(ch, Char.to_u32(ch), buf, nn, num, _)
        == Pull.WMore{ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch))} : Pull.Wst}
      sf = Equal.sym(Bool, Pull.word.special(Char.to_u32(ch)), False{}, spec_false(ch, hc))
      %sf : {Pull.word.keep.go(ch, Char.to_u32(ch), buf, nn, num, Bool.not(_))
        == Pull.WMore{ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch))} : Pull.Wst}
      {==}

# a word character grows the word
law decide_oth:
  for +ch: Char
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for hc: {Lex.classify(ch) == Lex.COther{} : Lex.Class}
  {Pull.word.decide(ch, Char.to_u32(ch), buf, nn, num)
    == Pull.WMore{ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch))} : Pull.Wst}

def decide_oth(ch, buf, nn, num, hc):
  decide_oth.at(ch, buf, nn, num, V.num.ok.digit(Char.to_u32(ch)), {==}, hc)

# a character that is not a word character ends the word
law decide_stop:
  for +ch: Char
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +hn: {M4.is_other(Lex.classify(ch)) == False{} : Bool}
  {Pull.word.decide(ch, Char.to_u32(ch), buf, nn, num) == Pull.WStop{buf, nn, num, ch} : Pull.Wst}

def decide_stop(ch, buf, nn, num, hn):
  ed = Equal.sym(Bool, V.num.ok.digit(Char.to_u32(ch)), False{}, dig_false(ch, hn))
  %ed : {Pull.word.digit.go(ch, Char.to_u32(ch), buf, nn, num, _) == Pull.WStop{buf, nn, num, ch} : Pull.Wst}
  st = Equal.sym(Bool, Pull.word.special(Char.to_u32(ch)), True{}, spec_true(ch, hn))
  %st : {Pull.word.keep.go(ch, Char.to_u32(ch), buf, nn, num, Bool.not(_)) == Pull.WStop{buf, nn, num, ch} : Pull.Wst}
  {==}

# a number's scan state after the characters of a string
def nfold(ws: String, num: V.Num) -> V.Num:
  match ws:
    case SNil{}:
      num
    case SCon{ch, tl}:
      nfold(tl, V.num.ok.step(num, Char.to_u32(ch)))

# the event a word's kind stands for
def aev(atom: Pull.Atom, raw: String, nn: U32) -> Pull.Ev:
  match atom:
    case Pull.ANull{}:
      Pull.ENull{}
    case Pull.ATrue{}:
      Pull.EBool{True{}}
    case Pull.AFalse{}:
      Pull.EBool{False{}}
    case Pull.ANum{}:
      Pull.ENum{raw, nn}
    case Pull.ABad{}:
      Pull.EErr{}

# whether a word's kind is not one
def is_abad(atom: Pull.Atom) -> Bool:
  match atom:
    case Pull.ABad{}:
      True{}
    case _:
      False{}

# a stopped word run stays stopped
law run_stopped:
  for +rr: String
  for buf: List<&2, Char>
  for nn: U32
  for num: V.Num
  for ch: Char
  {Pull.word.run(rr, Pull.WStop{buf, nn, num, ch}) == (rr, Pull.WStop{buf, nn, num, ch}) : (String & Pull.Wst)}

def run_stopped(rr, _buf, _nn, _num, _ch):
  match rr:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

# the first characters of the first characters are those
law take_take:
  for +src: String
  for +kk: Nat
  {D1.take(D1.take(src, kk), kk) == D1.take(src, kk) : String}

def take_take(src, kk):
  match src:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      match kk:
        case 0n:
          {==}
        case 1n+pp:
          Equal.cong(String, String, xx => SCon{hd, xx}, D1.take(D1.take(tl, pp), pp), D1.take(tl, pp),
            take_take(tl, pp))

# a span that holds a whole word compares as the word
law sp_w:
  for +ww: String
  for +nn: U32
  for +lit: String
  for h_tk: {D1.take(ww, U32.to_nat(nn)) == ww : String}
  {V.span.eq(ww, nn, lit) == String.eq(ww, lit) : Bool}

def sp_w(ww, nn, lit, h_tk):
  Equal.trans(Bool, V.span.eq(ww, nn, lit), String.eq(V.span.str(ww, nn, U32.is_zero(nn)), lit), String.eq(ww, lit),
    M1.span_eq_go(ww, U32.is_zero(nn), lit, nn),
    Equal.cong(String, Bool, xx => String.eq(xx, lit), V.span.str(ww, nn, U32.is_zero(nn)), ww,
      Equal.trans(String, V.span.str(ww, nn, U32.is_zero(nn)), D1.take(ww, U32.to_nat(nn)), ww,
        M13.span_take(ww, nn), h_tk)))

# a word's kind, told by its own spelling
def wk(+ww: String, num: V.Num) -> Pull.Atom:
  Pull.word.kind.go(num, String.eq(ww, "null"), String.eq(ww, "true"), String.eq(ww, "false"))

# a span that holds a whole word is of the word's kind
law kind_eq:
  for +ww: String
  for +nn: U32
  for +num: V.Num
  for +h_tk: {D1.take(ww, U32.to_nat(nn)) == ww : String}
  {Pull.word.kind(ww, nn, num) == wk(ww, num) : Pull.Atom}

def kind_eq(ww, nn, num, h_tk):
  e1 = Equal.sym(Bool, V.span.eq(ww, nn, "null"), String.eq(ww, "null"), sp_w(ww, nn, "null", h_tk))
  e2 = Equal.sym(Bool, V.span.eq(ww, nn, "true"), String.eq(ww, "true"), sp_w(ww, nn, "true", h_tk))
  e3 = Equal.sym(Bool, V.span.eq(ww, nn, "false"), String.eq(ww, "false"), sp_w(ww, nn, "false", h_tk))
  %e1 : {Pull.word.kind.go(num, _, V.span.eq(ww, nn, "true"), V.span.eq(ww, nn, "false")) == wk(ww, num) : Pull.Atom}
  %e2 : {Pull.word.kind.go(num, String.eq(ww, "null"), _, V.span.eq(ww, nn, "false")) == wk(ww, num) : Pull.Atom}
  %e3 : {Pull.word.kind.go(num, String.eq(ww, "null"), String.eq(ww, "true"), _) == wk(ww, num) : Pull.Atom}
  {==}

# the number scan over a string's characters
law nok_fold:
  for +ws: String
  for +num: V.Num
  {V.num.ok.go(String.to_list(ws), num) == V.num.ok.done(nfold(ws, num)) : Bool}

def nok_fold(ws, num):
  match ws:
    case SNil{}:
      {==}
    case SCon{+ch, +tl}:
      nok_fold(tl, V.num.ok.step(num, Char.to_u32(ch)))

# a span's text is all of its first characters
law tk_of:
  for +cut: String
  for +nn: U32
  for +bf: List<&2, Char>
  for +ww: String
  for e_r: {Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == bf : List<&2, Char>}
  for e_t: {Lex.text(bf) == ww : String}
  {D1.take(ww, U32.to_nat(nn)) == ww : String}

def tk_of(cut, nn, bf, ww, e_r, e_t):
  +kk = U32.to_nat(nn)
  +ew = Equal.trans(String, ww, Lex.text(bf), D1.take(cut, kk), Equal.sym(String, Lex.text(bf), ww, e_t),
    Equal.trans(String, Lex.text(bf), Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])), D1.take(cut, kk),
      Equal.cong(List<&2, Char>, String, xx => Lex.text(xx), bf, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []),
        Equal.sym(List<&2, Char>, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), bf, e_r)),
      Equal.trans(String, Lex.text(Lex.tokens.rev(cut, nn, U32.is_zero(nn), [])),
        V.span.str(cut, nn, U32.is_zero(nn)), D1.take(cut, kk),
        M2.text_span(cut, nn, U32.is_zero(nn)), M13.span_take(cut, nn))))
  Equal.trans(String, D1.take(ww, kk), D1.take(D1.take(cut, kk), kk), ww,
    Equal.cong(String, String, xx => D1.take(xx, kk), ww, D1.take(cut, kk), ew),
    Equal.trans(String, D1.take(D1.take(cut, kk), kk), D1.take(cut, kk), ww, take_take(cut, kk),
      Equal.sym(String, ww, D1.take(cut, kk), ew)))

# a lexer state between tokens with these tokens
def lxi(toks: List<&2, Lex.Tok>) -> Lex.Lex:
  Lex.Lex{Lex.Idle{}, [], toks}

# a lexer state in a word
def lxw(buf: List<&2, Char>, toks: List<&2, Lex.Tok>) -> Lex.Lex:
  Lex.Lex{Lex.Word{}, buf, toks}

# a lexer state's mode
def lxmode(lx: Lex.Lex) -> Lex.Mode:
  match lx:
    case Lex.Lex{md, _, _}:
      md

# the lexer mode a string mode of the cursor stands for
def mo(mode: Pull.Mode) -> Lex.Mode:
  match mode:
    case Pull.MQuote{}:
      Lex.Str{}
    case Pull.MSpan{_, _}:
      Lex.Str{}
    case Pull.MCopy{_}:
      Lex.Str{}
    case Pull.MEsc{_}:
      Lex.Esc{}
    case Pull.MUni{left, acc, _}:
      Lex.Uni{left, acc}
    case Pull.MHi{hi, _}:
      Lex.Hi{hi}
    case Pull.MHiEsc{hi, _}:
      Lex.HiEsc{hi}
    case Pull.MLo{left, acc, hi, _}:
      Lex.Lo{left, acc, hi}
    case _:
      Lex.Bad{}

# what a finished step must be: a failure, the end of a text that parses, or
# another event on a live cursor in step
def finok(t: String, stop: Pull.Stop, cur: Pull.Cur) -> Type:
  match stop:
    case Pull.SEv{Pull.EErr{}}:
      Unit
    case Pull.SEv{Pull.EEnd{}}:
      {D1.is_some(Ezjson.parse(t)) == True{} : Bool}
    case Pull.SEv{_}:
      M4.cinv(t, cur)
    case Pull.SSkip{}:
      Unit

# a string mode of the cursor in step: the lexer in the matching mode, the
# parser where it was when the string opened
def sminv(t: String, +x: String, mode: Pull.Mode, stack: List<&2, Pull.Frame>, done: Bool) -> Type:
  ({D1.short(x) == True{} : Bool} & ({done == False{} : Bool} & (&lx: Lex.Lex -> (M4.lx_e(t, x, lx)
    & ({lxmode(lx) == mo(mode) : Lex.Mode} & {M4.prel(stack, False{}, M4.pst(lx)) == True{} : Bool})))))

# a word the cursor is reading, in step: the lexer in the same word, the
# number scan and the span so far, and the parser before the word
def wminv(
  t: String,
  +x: String,
  +buf: List<&2, Char>,
  +nn: U32,
  num: V.Num,
  +stack: List<&2, Pull.Frame>,
  done: Bool
) -> Type:
  ({done == False{} : Bool} & ({Pull.expect.val.go(stack) == True{} : Bool} & ({D1.short(x) == True{} : Bool}
    & ({num == nfold(Lex.text(buf), V.NStart{}) : V.Num} & (&cut: String -> ({M12.sdrop(cut, nn, U32.is_zero(nn)) == x
      : String} & ({Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == buf : List<&2, Char>} & ({D1.short(cut) == True{}
        : Bool} & (&tk: List<&2, Lex.Tok> -> (M4.lx_e(t, x, Lex.Lex{Lex.Word{}, buf, tk})
          & {M4.prel(stack, False{}, M4.pst(Lex.Lex{Lex.Idle{}, [], tk})) == True{} : Bool}))))))))))

# a walking mode of the cursor in step
def cminv(t: String, x: String, mode: Pull.Mode, stack: List<&2, Pull.Frame>, dn: Bool) -> Type:
  match mode:
    case Pull.MIdle{}:
      M4.cinv(t, Pull.Cur{x, stack, dn, False{}})
    case Pull.MWord{buf, nn, num}:
      wminv(t, x, buf, nn, num, stack, dn)
    case Pull.MQuote{}:
      sminv(t, x, Pull.MQuote{}, stack, dn)
    case Pull.MSpan{cut, nn}:
      sminv(t, x, Pull.MSpan{cut, nn}, stack, dn)
    case Pull.MCopy{buf}:
      sminv(t, x, Pull.MCopy{buf}, stack, dn)
    case Pull.MEsc{buf}:
      sminv(t, x, Pull.MEsc{buf}, stack, dn)
    case Pull.MUni{left, acc, buf}:
      sminv(t, x, Pull.MUni{left, acc, buf}, stack, dn)
    case Pull.MHi{hi, buf}:
      sminv(t, x, Pull.MHi{hi, buf}, stack, dn)
    case Pull.MHiEsc{hi, buf}:
      sminv(t, x, Pull.MHiEsc{hi, buf}, stack, dn)
    case Pull.MLo{left, acc, hi, buf}:
      sminv(t, x, Pull.MLo{left, acc, hi, buf}, stack, dn)
    case _:
      Empty

# a walking step state in step, once it is known not to have finished
def sinv.g(
  t: String,
  x: String,
  mode: Pull.Mode,
  stack: List<&2, Pull.Frame>,
  goal: Pull.Goal,
  done: Bool,
  bad: Bool
) -> Type:
  match goal bad:
    case Pull.GNext{} False{}:
      cminv(t, x, mode, stack, done)
    case _ _:
      Empty

# a step state in step, by its mode
def sinv.m(
  t: String,
  +x: String,
  mode: Pull.Mode,
  +stack: List<&2, Pull.Frame>,
  +goal: Pull.Goal,
  +done: Bool,
  +bad: Bool
) -> Type:
  match mode:
    case Pull.MDone{stop, saved}:
      finok(t, stop, Pull.Cur{saved, stack, done, bad})
    case Pull.MRest{stop}:
      finok(t, stop, Pull.Cur{x, stack, done, bad})
    case other:
      sinv.g(t, x, other, stack, goal, done, bad)

# a step state of the cursor in step, with `x` left to read
def sinv(t: String, x: String, st: Pull.St) -> Type:
  match st:
    case Pull.S{mode, stack, goal, done, bad}:
      sinv.m(t, x, mode, stack, goal, done, bad)

# a reversal onto a list is the reversal, then the list
law rv_app:
  for +ee: List<&2, Lex.Tok>
  for +acc: List<&2, Lex.Tok>
  {List.reverse.go(&2, Lex.Tok, ee, acc) == List.append(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, ee, []), acc)
    : List<&2, Lex.Tok>}

def rv_app(ee, acc):
  match ee:
    case Nil{}:
      {==}
    case +hd <> +tl:
      +rt = List.reverse.go(&2, Lex.Tok, tl, [])
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, tl, hd <> acc), List.append(&2, Lex.Tok, rt,
        hd <> acc),
        List.append(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tl, [hd]), acc), rv_app(tl, hd <> acc),
        Equal.sym(List<&2, Lex.Tok>, List.append(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tl, [hd]), acc),
          List.append(&2, Lex.Tok, rt, hd <> acc), Equal.trans(List<&2, Lex.Tok>,
          List.append(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, tl, [hd]), acc),
          List.append(&2, Lex.Tok, List.append(&2, Lex.Tok, rt, [hd]), acc), List.append(&2, Lex.Tok, rt, hd <> acc),
          Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, xx => List.append(&2, Lex.Tok, xx, acc),
            List.reverse.go(&2, Lex.Tok, tl, [hd]), List.append(&2, Lex.Tok, rt, [hd]), rv_app(tl, [hd])),
          M8.lapp_assoc(rt, [hd], acc))))

# the parser after one more token
law pst_push:
  for +tok: Lex.Tok
  for +ee: List<&2, Lex.Tok>
  {Parse.run(M4.dens(List.reverse(&2, Lex.Tok, tok <> ee)), M4.pp0())
    == Parse.step(M4.den(tok), Parse.run(M4.dens(List.reverse(&2, Lex.Tok, ee)), M4.pp0())) : Parse.P}

def pst_push(tok, ee):
  +re = List.reverse(&2, Lex.Tok, ee)
  Equal.trans(Parse.P, Parse.run(M4.dens(List.reverse.go(&2, Lex.Tok, ee, [tok])), M4.pp0()),
    Parse.run(List.append(&2, Lex.Tok, M4.dens(re), [M4.den(tok)]), M4.pp0()),
    Parse.step(M4.den(tok), Parse.run(M4.dens(re), M4.pp0())),
    Equal.cong(List<&2, Lex.Tok>, Parse.P, xx => Parse.run(xx, M4.pp0()), M4.dens(List.reverse.go(&2, Lex.Tok, ee,
        [tok])),
      List.append(&2, Lex.Tok, M4.dens(re), [M4.den(tok)]),
      Equal.trans(List<&2, Lex.Tok>, M4.dens(List.reverse.go(&2, Lex.Tok, ee, [tok])),
        M4.dens(List.append(&2, Lex.Tok, re, [tok])), List.append(&2, Lex.Tok, M4.dens(re), [M4.den(tok)]),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, xx => M4.dens(xx), List.reverse.go(&2, Lex.Tok, ee, [tok]),
          List.append(&2, Lex.Tok, re, [tok]), rv_app(ee, [tok])), M2.dens_app(re, [tok]))),
    M9.prun_app(M4.dens(re), [M4.den(tok)], M4.pp0()))

# a value lands where the cursor lets it: the cursor after it, with the
# lexer state after it, is in step with the parser after the value is put
law land_c:
  for +tt: String
  for +rest: String
  for +lx: Lex.Lex
  for +stack: List<&2, Pull.Frame>
  for +qs: List<&2, Parse.Frame>
  for +root: Maybe<&2, V.Json>
  for +vv: V.Json
  for +h_s: {D1.short(rest) == True{} : Bool}
  for +e: M4.lx_e(tt, rest, lx)
  for +hc: {M4.cm(lx, rest) == True{} : Bool}
  for +hp: {M4.prel(stack, False{}, Parse.P{False{}, root, qs}) == True{} : Bool}
  for hv: {Pull.expect.val.go(stack) == True{} : Bool}
  for +eq: {M4.pst(lx) == Parse.put(qs, root, vv, False{}) : Parse.P}
  M4.cinv(tt, aft(rest, stack))

def land_c(tt, rest, lx, stack, qs, root, vv, h_s, e, hc, hp, hv, eq):
  match stack:
    case Nil{}:
      match qs:
        case Nil{}:
          match root:
            case None{}:
              (h_s, (lx, (e, (hc, Equal.trans(Bool, M4.prel([], True{}, M4.pst(lx)), M4.prel([], True{}, Parse.put([],
                  None{},
                vv,
                False{})), True{}, Equal.cong(Parse.P, Bool, xx => M4.prel([], True{}, xx), M4.pst(lx), Parse.put([],
                    None{},
                  vv,
                False{}), eq), {==})))))
            case Some{+rv}:
              M4.no(M4.cinv(tt, aft(rest, [])), M4.and_left(M4.rrel(False{}, Some{rv}, []), M4.frels([], []), hp))
        case +q <> +qt:
          M4.no(M4.cinv(tt, aft(rest, [])), M4.and_right(M4.rrel(False{}, root, []), M4.frels([], q <> qt), hp))
    case Pull.FArr{Pull.SVal{}, +fr} <> +st:
      match qs:
        case Nil{}:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_right(M4.rrel(False{}, root,
            Pull.FArr{Pull.SVal{}, fr} <> st), M4.frels(Pull.FArr{Pull.SVal{}, fr} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          match root:
            case None{}:
              (h_s, (lx, (e, (hc, Equal.trans(Bool, M4.prel(Pull.FArr{Pull.SCom{}, False{}} <> st, False{}, M4.pst(lx)),
                M4.prel(Pull.FArr{Pull.SCom{}, False{}} <> st, False{},
                Parse.put(Parse.FArr{items, Parse.SValue{}} <> qt, None{}, vv, False{})), True{}, Equal.cong(Parse.P,
                  Bool, xx => M4.prel(Pull.FArr{Pull.SCom{}, False{}} <> st, False{}, xx),
                M4.pst(lx), Parse.put(Parse.FArr{items, Parse.SValue{}} <> qt, None{}, vv, False{}), eq),
                  M4.and_right(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SValue{}}), M4.frels(st, qt),
                  M4.and_right(M4.rrel(False{}, None{}, Pull.FArr{Pull.SVal{}, fr} <> st),
                  Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SValue{}}), M4.frels(st, qt)),
                  hp)))))))
            case Some{+rv}:
              M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.rrel(False{}, Some{rv},
                Pull.FArr{Pull.SVal{}, fr} <> st), M4.frels(Pull.FArr{Pull.SVal{}, fr} <> st, Parse.FArr{items,
                Parse.SValue{}} <> qt), hp))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FArr{Pull.SVal{},
              fr},
            Parse.FArr{items, Parse.SComma{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SComma{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FArr{Pull.SVal{},
              fr},
            Parse.FArr{items, Parse.SKey{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SKey{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FArr{Pull.SVal{},
              fr},
            Parse.FArr{items, Parse.SColon{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SColon{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FArr{Pull.SVal{},
              fr},
            Parse.FObj{items, kk, Parse.SValue{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SValue{}}),
                M4.frels(st,
            qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FArr{Pull.SVal{},
              fr},
            Parse.FObj{items, kk, Parse.SComma{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}),
                M4.frels(st,
            qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FArr{Pull.SVal{},
              fr},
            Parse.FObj{items, kk, Parse.SKey{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FArr{Pull.SVal{},
              fr},
            Parse.FObj{items, kk, Parse.SColon{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FArr{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FArr{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}),
                M4.frels(st,
            qt)), hp)))
    case Pull.FArr{Pull.SCom{}, +fr} <> +st:
      M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SCom{}, fr} <> st)), hv)
    case Pull.FArr{Pull.SKey{}, +fr} <> +st:
      M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SKey{}, fr} <> st)), hv)
    case Pull.FArr{Pull.SCol{}, +fr} <> +st:
      M4.no(M4.cinv(tt, aft(rest, Pull.FArr{Pull.SCol{}, fr} <> st)), hv)
    case Pull.FObj{Pull.SVal{}, +fr} <> +st:
      match qs:
        case Nil{}:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_right(M4.rrel(False{}, root,
            Pull.FObj{Pull.SVal{}, fr} <> st), M4.frels(Pull.FObj{Pull.SVal{}, fr} <> st, []), hp))
        case Parse.FArr{+items, Parse.SValue{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FObj{Pull.SVal{},
              fr},
            Parse.FArr{items, Parse.SValue{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SValue{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FArr{+items, Parse.SComma{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FObj{Pull.SVal{},
              fr},
            Parse.FArr{items, Parse.SComma{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SComma{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FArr{+items, Parse.SKey{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FObj{Pull.SVal{},
              fr},
            Parse.FArr{items, Parse.SKey{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SKey{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FArr{+items, Parse.SColon{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FObj{Pull.SVal{},
              fr},
            Parse.FArr{items, Parse.SColon{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FArr{items, Parse.SColon{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FObj{+items, +kk, Parse.SValue{}} <> +qt:
          match root:
            case None{}:
              (h_s, (lx, (e, (hc, Equal.trans(Bool, M4.prel(Pull.FObj{Pull.SCom{}, False{}} <> st, False{}, M4.pst(lx)),
                M4.prel(Pull.FObj{Pull.SCom{}, False{}} <> st, False{},
                Parse.put(Parse.FObj{items, kk, Parse.SValue{}} <> qt, None{}, vv, False{})), True{},
                  Equal.cong(Parse.P, Bool, xx => M4.prel(Pull.FObj{Pull.SCom{}, False{}} <> st, False{}, xx),
                M4.pst(lx), Parse.put(Parse.FObj{items, kk, Parse.SValue{}} <> qt, None{}, vv, False{}), eq),
                  M4.and_right(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SValue{}}), M4.frels(st,
                      qt),
                  M4.and_right(M4.rrel(False{}, None{}, Pull.FObj{Pull.SVal{}, fr} <> st),
                  Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SValue{}}), M4.frels(st,
                      qt)),
                  hp)))))))
            case Some{+rv}:
              M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.rrel(False{}, Some{rv},
                Pull.FObj{Pull.SVal{}, fr} <> st), M4.frels(Pull.FObj{Pull.SVal{}, fr} <> st, Parse.FObj{items, kk,
                Parse.SValue{}} <> qt), hp))
        case Parse.FObj{+items, +kk, Parse.SComma{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FObj{Pull.SVal{},
              fr},
            Parse.FObj{items, kk, Parse.SComma{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SComma{}}),
                M4.frels(st,
            qt)), hp)))
        case Parse.FObj{+items, +kk, Parse.SKey{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FObj{Pull.SVal{},
              fr},
            Parse.FObj{items, kk, Parse.SKey{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SKey{}}), M4.frels(st,
                qt)),
            hp)))
        case Parse.FObj{+items, +kk, Parse.SColon{}} <> +qt:
          M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SVal{}, fr} <> st)), M4.and_left(M4.frel(Pull.FObj{Pull.SVal{},
              fr},
            Parse.FObj{items, kk, Parse.SColon{}}), M4.frels(st, qt), M4.and_right(M4.rrel(False{}, root,
                Pull.FObj{Pull.SVal{},
            fr} <> st), Bool.and(M4.frel(Pull.FObj{Pull.SVal{}, fr}, Parse.FObj{items, kk, Parse.SColon{}}),
                M4.frels(st,
            qt)), hp)))
    case Pull.FObj{Pull.SCom{}, +fr} <> +st:
      M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SCom{}, fr} <> st)), hv)
    case Pull.FObj{Pull.SKey{}, +fr} <> +st:
      M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SKey{}, fr} <> st)), hv)
    case Pull.FObj{Pull.SCol{}, +fr} <> +st:
      M4.no(M4.cinv(tt, aft(rest, Pull.FObj{Pull.SCol{}, fr} <> st)), hv)

# a parser in step has not failed: its root and frames, passed on
law pp_split:
  for gl: Type
  for +pp: Parse.P
  for +stack: List<&2, Pull.Frame>
  for hp: {M4.prel(stack, False{}, pp) == True{} : Bool}
  for kk: @root: Maybe<&2, V.Json> -> @qs: List<&2, Parse.Frame> -> {M4.prel(stack, False{}, Parse.P{False{}, root,
      qs}) ==
    True{} : Bool} -> {pp == Parse.P{False{}, root, qs} : Parse.P} -> gl
  gl

def pp_split(gl, pp, _stack, hp, kk):
  match pp:
    case Parse.P{True{}, _, _}:
      M4.no(gl, hp)
    case Parse.P{False{}, +root, +qs}:
      kk(root, qs, hp, {==})

# laws/CursorEventsMatchParse.bend, words in step with the lexer

# a buffer's text, then more
law tgo_app:
  for +buf: List<&2, Char>
  for +acc: String
  {Lex.text.go(buf, acc) == Lex.text.go(buf, "") ++ acc : String}

def tgo_app(buf, acc):
  match buf:
    case Nil{}:
      {==}
    case +hd <> +tl:
      Equal.trans(String, Lex.text.go(tl, SCon{hd, acc}), Lex.text.go(tl, "") ++ SCon{hd, acc},
        Lex.text.go(tl, SCon{hd, ""}) ++ acc, tgo_app(tl, SCon{hd, acc}),
        Equal.sym(String, Lex.text.go(tl, SCon{hd, ""}) ++ acc, Lex.text.go(tl, "") ++ SCon{hd, acc},
          Equal.trans(String, Lex.text.go(tl, SCon{hd, ""}) ++ acc, (Lex.text.go(tl, "") ++ SCon{hd, ""}) ++ acc,
            Lex.text.go(tl, "") ++ SCon{hd, acc},
            Equal.cong(String, String, xx => xx ++ acc, Lex.text.go(tl, SCon{hd, ""}), Lex.text.go(tl, "") ++ SCon{hd,
              ""},
              tgo_app(tl, SCon{hd, ""})), sassoc(Lex.text.go(tl, ""), SCon{hd, ""}, acc))))

# the number scan over a string and one more character
law nfold_snoc:
  for +aa: String
  for +ch: Char
  for +num: V.Num
  {nfold(aa ++ SCon{ch, ""}, num) == V.num.ok.step(nfold(aa, num), Char.to_u32(ch)) : V.Num}

def nfold_snoc(aa, ch, num):
  match aa:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      nfold_snoc(tl, ch, V.num.ok.step(num, Char.to_u32(hd)))

# the number scan of a word one character longer
law nfold_push:
  for +buf: List<&2, Char>
  for +ch: Char
  for +num: V.Num
  for hn: {num == nfold(Lex.text(buf), V.NStart{}) : V.Num}
  {V.num.ok.step(num, Char.to_u32(ch)) == nfold(Lex.text(ch <> buf), V.NStart{}) : V.Num}

def nfold_push(buf, ch, num, hn):
  Equal.trans(V.Num, V.num.ok.step(num, Char.to_u32(ch)), V.num.ok.step(nfold(Lex.text(buf), V.NStart{}),
    Char.to_u32(ch)), nfold(Lex.text(ch <> buf), V.NStart{}),
    Equal.cong(V.Num, V.Num, xx => V.num.ok.step(xx, Char.to_u32(ch)), num, nfold(Lex.text(buf), V.NStart{}), hn),
    Equal.sym(V.Num, nfold(Lex.text(ch <> buf), V.NStart{}), V.num.ok.step(nfold(Lex.text(buf), V.NStart{}),
      Char.to_u32(ch)), Equal.trans(V.Num, nfold(Lex.text.go(buf, SCon{ch, ""}), V.NStart{}),
      nfold(Lex.text(buf) ++ SCon{ch, ""}, V.NStart{}), V.num.ok.step(nfold(Lex.text(buf), V.NStart{}),
        Char.to_u32(ch)),
      Equal.cong(String, V.Num, xx => nfold(xx, V.NStart{}), Lex.text.go(buf, SCon{ch, ""}),
        Lex.text(buf) ++ SCon{ch, ""}, tgo_app(buf, SCon{ch, ""})), nfold_snoc(Lex.text(buf), ch, V.NStart{}))))

# a word kind other than none, once the literal tests are named: the parser takes the word
law done_ok:
  for dd: Bool
  for hk: {is_abad(Pull.word.kind.num(dd)) == False{} : Bool}
  {dd == True{} : Bool}

def done_ok(dd, hk):
  match dd:
    case True{}:
      {==}
    case False{}:
      M4.no({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, hk))

law kind_ok.at:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for +raw: String
  for +num: V.Num
  for +e1: {String.eq(raw, "null") == b1 : Bool}
  for +e2: {String.eq(raw, "true") == b2 : Bool}
  for +e3: {String.eq(raw, "false") == b3 : Bool}
  for +hn: {num == nfold(raw, V.NStart{}) : V.Num}
  for hk: {is_abad(Pull.word.kind.go(num, b1, b2, b3)) == False{} : Bool}
  {Parse.word.ok(raw) == True{} : Bool}

def kind_ok.at(b1, b2, b3, raw, num, e1, e2, e3, hn, hk):
  match b1 b2 b3:
    case True{} _ _:
      es = Equal.sym(Bool, String.eq(raw, "null"), True{}, e1)
      %es : {Bool.or(_, Bool.or(String.eq(raw, "true"), Bool.or(String.eq(raw, "false"),
        V.num.ok(raw)))) == True{} : Bool}
      {==}
    case False{} True{} _:
      es = Equal.sym(Bool, String.eq(raw, "null"), False{}, e1)
      %es : {Bool.or(_, Bool.or(String.eq(raw, "true"), Bool.or(String.eq(raw, "false"),
        V.num.ok(raw)))) == True{} : Bool}
      es2 = Equal.sym(Bool, String.eq(raw, "true"), True{}, e2)
      %es2 : {Bool.or(False{}, Bool.or(_, Bool.or(String.eq(raw, "false"), V.num.ok(raw)))) == True{} : Bool}
      {==}
    case False{} False{} True{}:
      es = Equal.sym(Bool, String.eq(raw, "null"), False{}, e1)
      %es : {Bool.or(_, Bool.or(String.eq(raw, "true"), Bool.or(String.eq(raw, "false"),
        V.num.ok(raw)))) == True{} : Bool}
      es2 = Equal.sym(Bool, String.eq(raw, "true"), False{}, e2)
      %es2 : {Bool.or(False{}, Bool.or(_, Bool.or(String.eq(raw, "false"), V.num.ok(raw)))) == True{} : Bool}
      es3 = Equal.sym(Bool, String.eq(raw, "false"), True{}, e3)
      %es3 : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, V.num.ok(raw)))) == True{} : Bool}
      {==}
    case False{} False{} False{}:
      es = Equal.sym(Bool, String.eq(raw, "null"), False{}, e1)
      %es : {Bool.or(_, Bool.or(String.eq(raw, "true"), Bool.or(String.eq(raw, "false"),
        V.num.ok(raw)))) == True{} : Bool}
      es2 = Equal.sym(Bool, String.eq(raw, "true"), False{}, e2)
      %es2 : {Bool.or(False{}, Bool.or(_, Bool.or(String.eq(raw, "false"), V.num.ok(raw)))) == True{} : Bool}
      es3 = Equal.sym(Bool, String.eq(raw, "false"), False{}, e3)
      %es3 : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, V.num.ok(raw)))) == True{} : Bool}
      Equal.trans(Bool, V.num.ok(raw), V.num.ok.done(nfold(raw, V.NStart{})), True{},
        nok_fold(raw, V.NStart{}), Equal.trans(Bool, V.num.ok.done(nfold(raw, V.NStart{})),
          V.num.ok.done(num), True{}, Equal.cong(V.Num, Bool, xx => V.num.ok.done(xx),
            nfold(raw, V.NStart{}), num, Equal.sym(V.Num, num, nfold(raw, V.NStart{}), hn)),
          done_ok(V.num.ok.done(num), hk)))

# a number kind other than none: the number scan finished well
# a word kind other than none: the parser takes the word
law kind_ok:
  for +raw: String
  for +nn: U32
  for +num: V.Num
  for h_tk: {D1.take(raw, U32.to_nat(nn)) == raw : String}
  for +hn: {num == nfold(raw, V.NStart{}) : V.Num}
  for hk: {is_abad(Pull.word.kind(raw, nn, num)) == False{} : Bool}
  {Parse.word.ok(raw) == True{} : Bool}

def kind_ok(raw, nn, num, h_tk, hn, hk):
  kind_ok.at(String.eq(raw, "null"), String.eq(raw, "true"), String.eq(raw, "false"), raw, num, {==}, {==}, {==}, hn,
    Equal.trans(Bool, is_abad(wk(raw, num)), is_abad(Pull.word.kind(raw, nn, num)), False{},
      Equal.cong(Pull.Atom, Bool, xx => is_abad(xx), wk(raw, num), Pull.word.kind(raw, nn, num),
        Equal.sym(Pull.Atom, Pull.word.kind(raw, nn, num), wk(raw, num), kind_eq(raw, nn, num, h_tk))), hk))

# is_other says a class is the word class
law oth_is:
  for cls: Lex.Class
  for h: {M4.is_other(cls) == True{} : Bool}
  {cls == Lex.COther{} : Lex.Class}

def oth_is(cls, h):
  match cls:
    case Lex.COther{}:
      {==}
    case Lex.CPunct{tt}:
      M4.no({Lex.CPunct{tt} == Lex.COther{} : Lex.Class}, h)
    case Lex.CQuote{}:
      M4.no({Lex.CQuote{} == Lex.COther{} : Lex.Class}, h)
    case Lex.CBack{}:
      M4.no({Lex.CBack{} == Lex.COther{} : Lex.Class}, h)
    case Lex.CSpace{}:
      M4.no({Lex.CSpace{} == Lex.COther{} : Lex.Class}, h)

# a word lands where a value may go: the step state is the cursor after it
law pv_bridge:
  for +tt: String
  for +atom: Pull.Atom
  for +raw: String
  for +nn: U32
  for +rest: String
  for +stack: List<&2, Pull.Frame>
  for hk: {is_abad(atom) == False{} : Bool}
  for cc: M4.cinv(tt, aft(rest, stack))
  sinv(tt, "", Pull.place.val(aev(atom, raw, nn), rest, stack, Pull.GNext{}))

def pv_bridge(tt, atom, raw, nn, rest, stack, hk, cc):
  match atom:
    case Pull.ANull{}:
      match stack:
        case Nil{}:
          cc
        case Pull.FArr{Pull.SVal{}, _} <> _:
          cc
        case Pull.FArr{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SCol{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SVal{}, _} <> _:
          cc
        case Pull.FObj{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SCol{}, _} <> _:
          Unit{}
    case Pull.ATrue{}:
      match stack:
        case Nil{}:
          cc
        case Pull.FArr{Pull.SVal{}, _} <> _:
          cc
        case Pull.FArr{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SCol{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SVal{}, _} <> _:
          cc
        case Pull.FObj{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SCol{}, _} <> _:
          Unit{}
    case Pull.AFalse{}:
      match stack:
        case Nil{}:
          cc
        case Pull.FArr{Pull.SVal{}, _} <> _:
          cc
        case Pull.FArr{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SCol{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SVal{}, _} <> _:
          cc
        case Pull.FObj{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SCol{}, _} <> _:
          Unit{}
    case Pull.ANum{}:
      match stack:
        case Nil{}:
          cc
        case Pull.FArr{Pull.SVal{}, _} <> _:
          cc
        case Pull.FArr{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FArr{Pull.SCol{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SVal{}, _} <> _:
          cc
        case Pull.FObj{Pull.SCom{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SKey{}, _} <> _:
          Unit{}
        case Pull.FObj{Pull.SCol{}, _} <> _:
          Unit{}
    case Pull.ABad{}:
      M4.no(sinv(tt, "", Pull.place.val(aev(Pull.ABad{}, raw, nn), rest, stack, Pull.GNext{})), Equal.sym(Bool, True{},
        False{}, hk))

# a word lands where a value may go: the cursor after it is in step
law wland:
  for +tt: String
  for +rest: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(rest) == True{} : Bool}
  for +e: M4.lx_e(tt, rest, lxw(buf, tk))
  for +hc: {M4.cm(lxw(buf, tk), rest) == True{} : Bool}
  for +hv: {Pull.expect.val.go(stack) == True{} : Bool}
  for +hp: {M4.prel(stack, False{}, M4.pst(lxi(tk))) == True{} : Bool}
  for +h_tk: {D1.take(Lex.text(buf), U32.to_nat(nn)) == Lex.text(buf) : String}
  for +hn: {num == nfold(Lex.text(buf), V.NStart{}) : V.Num}
  for +hk: {is_abad(Pull.word.kind(Lex.text(buf), nn, num)) == False{} : Bool}
  M4.cinv(tt, aft(rest, stack))

def wland(tt, rest, buf, nn, num, stack, tk, h_s, e, hc, hv, hp, h_tk, hn, hk):
  +raw = Lex.text(buf)
  +hok = kind_ok(raw, nn, num, h_tk, hn, hk)
  pp_split(M4.cinv(tt, aft(rest, stack)), M4.pst(lxi(tk)), stack, hp, +root => +qs => hp2 => epp => land_c(tt, rest,
    lxw(buf, tk), stack, qs, root, Parse.word(raw), h_s, e, hc, hp2, hv, Equal.trans(Parse.P, M4.pst(lxw(buf, tk)),
      Parse.step(Lex.TWord{raw}, Parse.P{False{}, root, qs}), Parse.put(qs, root, Parse.word(raw), False{}),
      Equal.trans(Parse.P, M4.pst(lxw(buf, tk)), Parse.step(Lex.TWord{raw}, M4.pst(lxi(tk))),
        Parse.step(Lex.TWord{raw}, Parse.P{False{}, root, qs}), pst_push(Lex.TWord{raw}, tk),
        Equal.cong(Parse.P, Parse.P, zz => Parse.step(Lex.TWord{raw}, zz), M4.pst(lxi(tk)), Parse.P{False{}, root, qs},
          epp)),
      Equal.cong(Bool, Parse.P, zz => Parse.step.word.go(raw, Parse.P{False{}, root, qs}, zz), Parse.word.ok(raw),
        True{}, hok))))

# a word ended by the end of the text lands
law wb_eof:
  for +tt: String
  for +rest: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(rest) == True{} : Bool}
  for +e: M4.lx_e(tt, rest, lxw(buf, tk))
  for +hc: {M4.cm(lxw(buf, tk), rest) == True{} : Bool}
  for +hv: {Pull.expect.val.go(stack) == True{} : Bool}
  for +hp: {M4.prel(stack, False{}, M4.pst(lxi(tk))) == True{} : Bool}
  for +h_tk: {D1.take(Lex.text(buf), U32.to_nat(nn)) == Lex.text(buf) : String}
  for +hn: {num == nfold(Lex.text(buf), V.NStart{}) : V.Num}
  for +eqr: {rest == "" : String}
  for +atom: Pull.Atom
  for +ek: {Pull.word.kind(Lex.text(buf), nn, num) == atom : Pull.Atom}
  sinv(tt, "", Pull.word.eof.place(atom, Lex.text(buf), nn, stack, Pull.GNext{}))

def wb_eof(tt, rest, buf, nn, num, stack, tk, h_s, e, hc, hv, hp, h_tk, hn, eqr, atom, ek):
  match atom:
    case Pull.ABad{}:
      Unit{}
    case Pull.ANull{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.ANull{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.ANull{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s,
        e, hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)),
        is_abad(Pull.ANull{}), False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf),
        nn, num), Pull.ANull{}, ek), {==})))
    case Pull.ATrue{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.ATrue{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.ATrue{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s,
        e, hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)),
        is_abad(Pull.ATrue{}), False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf),
        nn, num), Pull.ATrue{}, ek), {==})))
    case Pull.AFalse{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.AFalse{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.AFalse{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s,
        e, hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)),
        is_abad(Pull.AFalse{}), False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf),
        nn, num), Pull.AFalse{}, ek), {==})))
    case Pull.ANum{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.ANum{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.ANum{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s, e,
        hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)), is_abad(Pull.ANum{}),
        False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf), nn, num), Pull.ANum{},
        ek), {==})))

# a word ended by a delimiter lands, the delimiter left to read
law wb_stop:
  for +tt: String
  for +rest: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +tk: List<&2, Lex.Tok>
  for +h_s: {D1.short(rest) == True{} : Bool}
  for +e: M4.lx_e(tt, rest, lxw(buf, tk))
  for +hc: {M4.cm(lxw(buf, tk), rest) == True{} : Bool}
  for +hv: {Pull.expect.val.go(stack) == True{} : Bool}
  for +hp: {M4.prel(stack, False{}, M4.pst(lxi(tk))) == True{} : Bool}
  for +h_tk: {D1.take(Lex.text(buf), U32.to_nat(nn)) == Lex.text(buf) : String}
  for +hn: {num == nfold(Lex.text(buf), V.NStart{}) : V.Num}
  for +ch: Char
  for +rr: String
  for +eqr: {rest == SCon{ch, rr} : String}
  for +atom: Pull.Atom
  for +ek: {Pull.word.kind(Lex.text(buf), nn, num) == atom : Pull.Atom}
  sinv(tt, "", Pull.word.burst.atom(rr, ch, Lex.text(buf), nn, stack, Pull.GNext{}, atom))

def wb_stop(tt, rest, buf, nn, num, stack, tk, h_s, e, hc, hv, hp, h_tk, hn, _ch, _rr, eqr, atom, ek):
  match atom:
    case Pull.ABad{}:
      Unit{}
    case Pull.ANull{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.ANull{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.ANull{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s,
        e, hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)),
        is_abad(Pull.ANull{}), False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf),
        nn, num), Pull.ANull{}, ek), {==})))
    case Pull.ATrue{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.ATrue{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.ATrue{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s,
        e, hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)),
        is_abad(Pull.ATrue{}), False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf),
        nn, num), Pull.ATrue{}, ek), {==})))
    case Pull.AFalse{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.AFalse{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.AFalse{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s,
        e, hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)),
        is_abad(Pull.AFalse{}), False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf),
        nn, num), Pull.AFalse{}, ek), {==})))
    case Pull.ANum{}:
      %eqr : sinv(tt, "", Pull.place.val(aev(Pull.ANum{}, Lex.text(buf), nn), _, stack, Pull.GNext{}))
      pv_bridge(tt, Pull.ANum{}, Lex.text(buf), nn, rest, stack, {==}, wland(tt, rest, buf, nn, num, stack, tk, h_s, e,
        hc, hv, hp, h_tk, hn, Equal.trans(Bool, is_abad(Pull.word.kind(Lex.text(buf), nn, num)), is_abad(Pull.ANum{}),
        False{}, Equal.cong(Pull.Atom, Bool, zz => is_abad(zz), Pull.word.kind(Lex.text(buf), nn, num), Pull.ANum{},
        ek), {==})))

# a word's characters, once whether the next one is a word character is named
law wb.at:
  for +tt: String
  for +ch: Char
  for +rr: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +tk: List<&2, Lex.Tok>
  for +cut: String
  for +hv: {Pull.expect.val.go(stack) == True{} : Bool}
  for +hsx: {D1.short(SCon{ch, rr}) == True{} : Bool}
  for +hn: {num == nfold(Lex.text(buf), V.NStart{}) : V.Num}
  for +e_d: {M12.sdrop(cut, nn, U32.is_zero(nn)) == SCon{ch, rr} : String}
  for +e_r: {Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == buf : List<&2, Char>}
  for +h_c: {D1.short(cut) == True{} : Bool}
  for +e: M4.lx_e(tt, SCon{ch, rr}, lxw(buf, tk))
  for +hp: {M4.prel(stack, False{}, M4.pst(lxi(tk))) == True{} : Bool}
  for ob: Bool
  for +eob: {M4.is_other(Lex.classify(ch)) == ob : Bool}
  for ih: @buf2: List<&2, Char> -> @nn2: U32 -> @num2: V.Num -> {num2 == nfold(Lex.text(buf2), V.NStart{}) : V.Num} ->
    {M12.sdrop(cut, nn2, U32.is_zero(nn2)) == rr : String} -> {Lex.tokens.rev(cut, nn2, U32.is_zero(nn2), []) == buf2
    : List<&2, Char>} -> M4.lx_e(tt, rr, lxw(buf2, tk)) -> sinv(tt, "", Pull.word.burst(rr, buf2, nn2, num2, stack,
    Pull.GNext{}, False{}))
  sinv(tt, "", Pull.word.burst(SCon{ch, rr}, buf, nn, num, stack, Pull.GNext{}, False{}))

def wb.at(tt, ch, rr, buf, nn, num, stack, tk, cut, hv, hsx, hn, e_d, e_r, h_c, e, hp, ob, eob, ih):
  match ob:
    case True{}:
      +hc = oth_is(Lex.classify(ch), eob)
      ed = Equal.sym(Pull.Wst, Pull.word.decide(ch, Char.to_u32(ch), buf, nn, num), Pull.WMore{ch <> buf, U32.add(nn,
        1),
        V.num.ok.step(num, Char.to_u32(ch))}, decide_oth(ch, buf, nn, num, hc))
      %ed : sinv(tt, "", Pull.word.burst.at(Pull.word.run(rr, _), stack, Pull.GNext{}))
      +top = M2.pos_ne(cut, nn, 4294967295, U32.is_zero(nn), {==}, h_c, ch, rr, e_d)
      ih(ch <> buf, U32.add(nn, 1), V.num.ok.step(num, Char.to_u32(ch)), nfold_push(buf, ch, num, hn),
        M2.sdrop_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, rr, e_d),
        Equal.trans(List<&2, Char>, Lex.tokens.rev(cut, U32.add(nn, 1), U32.is_zero(U32.add(nn, 1)), []),
          ch <> Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), ch <> buf,
          M2.rev_grow(cut, nn, U32.is_zero(nn), {==}, top, ch, rr, e_d, []),
          Equal.cong(List<&2, Char>, List<&2, Char>, xx => ch <> xx, Lex.tokens.rev(cut, nn, U32.is_zero(nn), []), buf,
            e_r)),
        Equal.trans(Lex.Lex, Lex.run(String.to_list(tt), M4.lx0()), Lex.run(String.to_list(rr), Lex.step(Lex.Word{},
          Lex.classify(ch), ch, buf, tk)), Lex.run(String.to_list(rr), lxw(ch <> buf, tk)), e,
          Equal.cong(Lex.Class, Lex.Lex, xx => Lex.run(String.to_list(rr), Lex.step(Lex.Word{}, xx, ch, buf, tk)),
            Lex.classify(ch), Lex.COther{}, hc)))
    case False{}:
      ed = Equal.sym(Pull.Wst, Pull.word.decide(ch, Char.to_u32(ch), buf, nn, num), Pull.WStop{buf, nn, num, ch},
        decide_stop(ch, buf, nn, num, eob))
      %ed : sinv(tt, "", Pull.word.burst.at(Pull.word.run(rr, _), stack, Pull.GNext{}))
      rs = Equal.sym((String & Pull.Wst), Pull.word.run(rr, Pull.WStop{buf, nn, num, ch}), (rr, Pull.WStop{buf, nn, num,
        ch}), run_stopped(rr, buf, nn, num, ch))
      %rs : sinv(tt, "", Pull.word.burst.at(_, stack, Pull.GNext{}))
      wb_stop(tt, SCon{ch, rr}, buf, nn, num, stack, tk, hsx, e, Equal.cong(Bool, Bool, xx => Bool.not(xx),
        M4.is_other(Lex.classify(ch)), False{}, eob), hv, hp, tk_of(cut, nn, buf, Lex.text(buf), e_r, {==}), hn, ch, rr,
        {==}, Pull.word.kind(Lex.text(buf), nn, num), {==})

# a word's characters, to its delimiter or the text's end: it lands in step, or fails
law wb:
  for +tt: String
  for +xx: String
  for +buf: List<&2, Char>
  for +nn: U32
  for +num: V.Num
  for +stack: List<&2, Pull.Frame>
  for +tk: List<&2, Lex.Tok>
  for +cut: String
  for +hv: {Pull.expect.val.go(stack) == True{} : Bool}
  for +hsx: {D1.short(xx) == True{} : Bool}
  for +hn: {num == nfold(Lex.text(buf), V.NStart{}) : V.Num}
  for +e_d: {M12.sdrop(cut, nn, U32.is_zero(nn)) == xx : String}
  for +e_r: {Lex.tokens.rev(cut, nn, U32.is_zero(nn), []) == buf : List<&2, Char>}
  for +h_c: {D1.short(cut) == True{} : Bool}
  for +e: M4.lx_e(tt, xx, lxw(buf, tk))
  for +hp: {M4.prel(stack, False{}, M4.pst(lxi(tk))) == True{} : Bool}
  sinv(tt, "", Pull.word.burst(xx, buf, nn, num, stack, Pull.GNext{}, False{}))

def wb(tt, xx, buf, nn, num, stack, tk, cut, hv, hsx, hn, e_d, e_r, h_c, e, hp):
  match xx:
    case SNil{}:
      wb_eof(tt, "", buf, nn, num, stack, tk, {==}, e, {==}, hv, hp, tk_of(cut, nn, buf, Lex.text(buf), e_r, {==}), hn,
        {==}, Pull.word.kind(Lex.text(buf), nn, num), {==})
    case SCon{+ch, +rr}:
      wb.at(tt, ch, rr, buf, nn, num, stack, tk, cut, hv, hsx, hn, e_d, e_r, h_c, e, hp, M4.is_other(Lex.classify(ch)),
        {==}, +b2 => +n2 => +m2 => hn2 => ed2 => er2 => e2 => wb(tt, rr, b2, n2, m2, stack, tk, cut, hv,
          M2.short_tail(ch, rr, hsx), hn2, ed2, er2, h_c, e2, hp))
