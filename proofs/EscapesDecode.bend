# proofs of laws/EscapesDecode.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../laws/EscapesDecode.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ../laws/defs/GrammarDerivations.bend as D2
import ./lemmas/ArrayLength.bend as M1
import ./lemmas/CharacterClasses.bend as M2
import ./lemmas/CharacterScan.bend as M3
import ./lemmas/ErrorToken.bend as M4
import ./lemmas/LexemeOrder.bend as M5
import ./lemmas/LexerErrorSticks.bend as M6
import ./lemmas/OwnedParse.bend as M7
import ./lemmas/StringTokens.bend as M8

# the character after a backslash, when it is no escape at all
law esc_to_bad:
  for +uu: U32
  for +bf: List<&2, Char>
  for h_u: {U32.is_eq(uu, 117) == False{} : Bool}
  for h_e: {D2.unesc(Chr{uu}) == None{} : Maybe<&2, Char>}
  {Lex.feed(Chr{uu}, Lex.Lex{Lex.Esc{}, bf, []}) == Lex.Lex{Lex.Bad{}, [], []} : Lex.Lex}

def esc_to_bad(uu, bf, h_u, h_e):
  hu = Equal.sym(Bool, U32.is_eq(uu, 117), False{}, h_u)
  %hu : {Lex.escape.go(Chr{uu}, bf, [], _) == Lex.Lex{Lex.Bad{}, [], []} : Lex.Lex}
  es = Equal.sym(Maybe<&2, Char>, D2.unesc(Chr{uu}), None{}, h_e)
  %es : {Lex.escape.put(_, bf, []) == Lex.Lex{Lex.Bad{}, [], []} : Lex.Lex}
  {==}

# the decoded string, read back from the buffer
law esc_text:
  for +pre: String
  for +cc: Char
  for +post: String
  {Lex.text(List.reverse.go(&2, Char, String.to_list(post), cc <> List.reverse.go(&2, Char, String.to_list(pre),
    []))) == pre ++ SCon{cc, post} : String}

def esc_text(pre, cc, post):
  Equal.trans(String, Lex.text(List.reverse.go(&2, Char, String.to_list(post), cc <> List.reverse.go(&2, Char,
    String.to_list(pre), []))), Lex.text.go(List.reverse.go(&2, Char, String.to_list(pre), []), SCon{cc,
    String.from_list(String.to_list(post)) ++ ""}), pre ++ SCon{cc, post}, M5.text_revgo(String.to_list(post),
    cc <> List.reverse.go(&2, Char, String.to_list(pre), []), ""),
    Equal.trans(String, Lex.text.go(List.reverse.go(&2, Char, String.to_list(pre), []), SCon{cc,
      String.from_list(String.to_list(post)) ++ ""}), String.from_list(String.to_list(pre)) ++ SCon{cc,
      String.from_list(String.to_list(post)) ++ ""}, pre ++ SCon{cc, post}, M5.text_revgo(String.to_list(pre), [],
      SCon{cc, String.from_list(String.to_list(post)) ++ ""}),
    Equal.trans(String, String.from_list(String.to_list(pre)) ++ SCon{cc,
      String.from_list(String.to_list(post)) ++ ""}, pre ++ SCon{cc, String.from_list(String.to_list(post)) ++ ""},
      pre ++ SCon{cc, post},
    Equal.cong(String, String, zz => zz ++ SCon{cc, String.from_list(String.to_list(post)) ++ ""},
      String.from_list(String.to_list(pre)), pre, M5.from_to(pre)),
    Equal.cong(String, String, zz => pre ++ SCon{cc, zz}, String.from_list(String.to_list(post)) ++ "", post,
      Equal.trans(String, String.from_list(String.to_list(post)) ++ "", String.from_list(String.to_list(post)), post,
        M5.append_nil(String.from_list(String.to_list(post))),
        M5.from_to(post))))))

# the character lexer on a string with a two-character escape
law esc_lex:
  for +pre: String
  for +uu: U32
  for +cc: Char
  for +post: String
  for +h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_e: {D2.unesc(Chr{uu}) == Some{cc} : Maybe<&2, Char>}
  for +h_q: {D1.raw_ok(String.to_list(post)) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\""), Lex.Lex{Lex.Idle{}, [],
    []})) == [Lex.TStr{pre ++ SCon{cc, post}}] : List<&2, Lex.Tok>}

def esc_lex(pre, uu, cc, post, h_p, h_e, h_q):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu},
    post}} ++ "\""), Lex.Lex{Lex.Idle{}, [], []})), Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{Chr{uu},
    post}} ++ "\""), Lex.Lex{Lex.Str{}, [], []})), [Lex.TStr{pre ++ SCon{cc, post}}], Equal.cong(Lex.Lex, List<&2,
    Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\""),
    Lex.Lex{Lex.Idle{}, [], []}), Lex.run(String.to_list(pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\""),
    Lex.Lex{Lex.Str{}, [], []}),
    M8.seq("\"", pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\"", Lex.Lex{Lex.Idle{}, [], []}, Lex.Lex{Lex.Str{}, [],
        []},
      {==})),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\""),
      Lex.Lex{Lex.Str{}, [], []})), Lex.finish(Lex.run(String.to_list(SCon{'\\', SCon{Chr{uu}, post}} ++ "\""),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []})), [Lex.TStr{pre ++ SCon{cc, post}}],
      Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list(pre ++ SCon{'\\',
      SCon{Chr{uu}, post}} ++ "\""), Lex.Lex{Lex.Str{}, [], []}), Lex.run(String.to_list(SCon{'\\', SCon{Chr{uu},
      post}} ++ "\""), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []}),
    M8.seq(pre, SCon{'\\', SCon{Chr{uu}, post}} ++ "\"", Lex.Lex{Lex.Str{}, [], []}, Lex.Lex{Lex.Str{},
      List.reverse.go(&2, Char, String.to_list(pre), []), []}, M8.lex_raw(String.to_list(pre), h_p, [], []))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(SCon{'\\', SCon{Chr{uu}, post}} ++ "\""),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []})),
      Lex.finish(Lex.run(String.to_list(post ++ "\""), Lex.Lex{Lex.Str{}, cc <> List.reverse.go(&2, Char,
      String.to_list(pre), []), []})), [Lex.TStr{pre ++ SCon{cc, post}}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
      zz => Lex.finish(Lex.run(String.to_list(post ++ "\""), zz)), Lex.feed(Chr{uu}, Lex.Lex{Lex.Esc{},
      List.reverse.go(&2, Char, String.to_list(pre), []), []}),
    Lex.Lex{Lex.Str{}, cc <> List.reverse.go(&2, Char, String.to_list(pre), []), []}, M3.esc_to(U32.is_eq(uu, 117), uu,
      cc, List.reverse.go(&2, Char, String.to_list(pre), []), {==}, h_e)),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(post ++ "\""), Lex.Lex{Lex.Str{},
      cc <> List.reverse.go(&2, Char, String.to_list(pre), []), []})), Lex.finish(Lex.run(String.to_list("\""),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(post), cc <> List.reverse.go(&2, Char,
      String.to_list(pre), [])), []})), [Lex.TStr{pre ++ SCon{cc, post}}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
      zz => Lex.finish(zz), Lex.run(String.to_list(post ++ "\""), Lex.Lex{Lex.Str{}, cc <> List.reverse.go(&2, Char,
      String.to_list(pre), []), []}), Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
      String.to_list(post), cc <> List.reverse.go(&2, Char, String.to_list(pre), [])), []}),
    M8.seq(post, "\"", Lex.Lex{Lex.Str{}, cc <> List.reverse.go(&2, Char, String.to_list(pre), []), []},
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(post), cc <> List.reverse.go(&2, Char,
      String.to_list(pre), [])), []}, M8.lex_raw(String.to_list(post), h_q, cc <> List.reverse.go(&2, Char,
      String.to_list(pre), []), []))),
    Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TStr{zz}], Lex.text(List.reverse.go(&2, Char,
      String.to_list(post), cc <> List.reverse.go(&2, Char, String.to_list(pre), []))), pre ++ SCon{cc, post},
      esc_text(pre, cc, post))))))

def Laws.esc_decodes(pre, ch, cc, post, h_p, h_e, h_q, h_s):
  match ch:
    case Chr{+uu}:
      M8.one_str(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\""), pre ++ SCon{cc, post},
        Equal.trans(List<&2, Lex.Tok>, M5.dens(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\"")),
        M5.dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\""),
        Lex.Lex{Lex.Idle{}, [], []}))),
        [Lex.TStr{pre ++ SCon{cc, post}}], M2.lexers_agree("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\"", h_s),
        Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M5.dens(zz),
          Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, post}} ++ "\""),
          Lex.Lex{Lex.Idle{}, [], []})), [Lex.TStr{pre ++ SCon{cc, post}}],
          esc_lex(pre, uu, cc, post, h_p, h_e, h_q))))

# the character lexer on a string with a bad escape
law esc_bad_lex:
  for +pre: String
  for +uu: U32
  for +rest: String
  for +h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_u: {U32.is_eq(uu, 117) == False{} : Bool}
  for +h_e: {D2.unesc(Chr{uu}) == None{} : Maybe<&2, Char>}
  {Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}), Lex.Lex{Lex.Idle{}, [],
    []})) == [Lex.TBad{}] : List<&2, Lex.Tok>}

def esc_bad_lex(pre, uu, rest, h_p, h_u, h_e):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
    Lex.Lex{Lex.Idle{}, [], []})), Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
    Lex.Lex{Lex.Str{}, [], []})), [Lex.TBad{}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz),
    Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}), Lex.Lex{Lex.Idle{}, [], []}),
    Lex.run(String.to_list(pre ++ SCon{'\\', SCon{Chr{uu}, rest}}), Lex.Lex{Lex.Str{}, [], []}),
    M8.seq("\"", pre ++ SCon{'\\', SCon{Chr{uu}, rest}}, Lex.Lex{Lex.Idle{}, [], []}, Lex.Lex{Lex.Str{}, [], []},
        {==})),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
      Lex.Lex{Lex.Str{}, [], []})), Lex.finish(Lex.run(String.to_list(SCon{'\\', SCon{Chr{uu}, rest}}),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []})), [Lex.TBad{}], Equal.cong(Lex.Lex,
      List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list(pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
      Lex.Lex{Lex.Str{}, [], []}), Lex.run(String.to_list(SCon{'\\', SCon{Chr{uu}, rest}}), Lex.Lex{Lex.Str{},
      List.reverse.go(&2, Char, String.to_list(pre), []), []}),
    M8.seq(pre, SCon{'\\', SCon{Chr{uu}, rest}}, Lex.Lex{Lex.Str{}, [], []}, Lex.Lex{Lex.Str{}, List.reverse.go(&2,
        Char,
      String.to_list(pre), []), []}, M8.lex_raw(String.to_list(pre), h_p, [], []))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(SCon{'\\', SCon{Chr{uu}, rest}}),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []})),
      Lex.finish(Lex.run(String.to_list(rest), Lex.Lex{Lex.Bad{}, [], []})), [Lex.TBad{}], Equal.cong(Lex.Lex, List<&2,
      Lex.Tok>, zz => Lex.finish(Lex.run(String.to_list(rest), zz)), Lex.feed(Chr{uu}, Lex.Lex{Lex.Esc{},
      List.reverse.go(&2, Char, String.to_list(pre), []), []}),
    Lex.Lex{Lex.Bad{}, [], []}, esc_to_bad(uu, List.reverse.go(&2, Char, String.to_list(pre), []), h_u, h_e)),
    Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list(rest), Lex.Lex{Lex.Bad{}, [],
      []}), Lex.Lex{Lex.Bad{}, [], []}, M6.bad_run(String.to_list(rest))))))

def Laws.esc_bad(pre, ch, rest, h_p, h_e, h_u, h_s):
  match ch:
    case Chr{+uu}:
      M6.own_m_none(Ezjson.parse("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
        Equal.trans(Maybe<&2, V.Json>, D1.own_m(Parse.finish(Parse.run(Lex.tokens("\"" ++ pre ++ SCon{'\\',
          SCon{Chr{uu}, rest}}), Parse.P{False{}, None{}, Nil{}}))),
          Parse.finish(M7.ownp(Parse.run(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}), Parse.P{False{},
          None{}, Nil{}}))), None{}, M7.fin_own(Parse.run(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
          Parse.P{False{}, None{}, Nil{}})),
          Equal.trans(Maybe<&2, V.Json>, Parse.finish(M7.ownp(Parse.run(Lex.tokens("\"" ++ pre ++ SCon{'\\',
              SCon{Chr{uu},
            rest}}), Parse.P{False{}, None{}, Nil{}}))),
            Parse.finish(Parse.run(M5.dens(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}})), Parse.P{False{},
            None{}, Nil{}})), None{}, Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz),
            M7.ownp(Parse.run(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}), Parse.P{False{}, None{},
            Nil{}})), Parse.run(M5.dens(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}})), Parse.P{False{},
            None{}, Nil{}}),
          M7.run_own(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}), Parse.P{False{}, None{}, Nil{}})),
          Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M5.dens(Lex.tokens("\"" ++ pre ++ SCon{'\\',
              SCon{Chr{uu},
            rest}})), Parse.P{False{}, None{}, Nil{}})),
            Parse.finish(Parse.run(M5.dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu},
            rest}}), Lex.Lex{Lex.Idle{}, [], []}))), Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(List<&2,
            Lex.Tok>, Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(zz, Parse.P{False{}, None{}, Nil{}})),
            M5.dens(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}})),
            M5.dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
                Lex.Lex{Lex.Idle{},
            [], []}))), M2.lexers_agree("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}, h_s)),
          M4.bad_none(M5.dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
            Lex.Lex{Lex.Idle{}, [], []}))), Parse.P{False{}, None{}, Nil{}}, Equal.trans(Bool,
            M4.has_bad(M5.dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
            Lex.Lex{Lex.Idle{}, [], []})))), M4.has_bad(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\',
            SCon{Chr{uu}, rest}}), Lex.Lex{Lex.Idle{}, [], []}))), True{},
            M4.hb_dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}),
            Lex.Lex{Lex.Idle{}, [], []}))),
          Equal.cong(List<&2, Lex.Tok>, Bool, zz => M4.has_bad(zz),
            Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{Chr{uu}, rest}}), Lex.Lex{Lex.Idle{}, [],
            []})), [Lex.TBad{}], esc_bad_lex(pre, uu, rest, h_p, h_u, h_e))))))))

# the character lexer on a string with a \u escape
law esc_u_lex:
  for +pre: String
  for +aa: Char
  for +bb: Char
  for +cc: Char
  for +dd: Char
  for +post: String
  for +h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_h: {Bool.and(D2.hexd(aa), Bool.and(D2.hexd(bb), Bool.and(D2.hexd(cc), D2.hexd(dd)))) == True{} : Bool}
  for +h_n: {D2.non_sur(D2.hex4(aa, bb, cc, dd)) == True{} : Bool}
  for +h_q: {D1.raw_ok(String.to_list(post)) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
    post}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [], []})) == [Lex.TStr{pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)},
    post}}] : List<&2, Lex.Tok>}

def esc_u_lex(pre, aa, bb, cc, dd, post, h_p, h_h, h_n, h_q):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa,
    SCon{bb, SCon{cc, SCon{dd, post}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [], []})),
    Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
    post ++ "\""}}}}}}), Lex.Lex{Lex.Str{}, [], []})), [Lex.TStr{pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)}, post}}],
    Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\',
    SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [], []}),
    Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post ++ "\""}}}}}}),
    Lex.Lex{Lex.Str{}, [], []}),
    M8.seq("\"", pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post ++ "\""}}}}}}, Lex.Lex{Lex.Idle{},
      [], []}, Lex.Lex{Lex.Str{}, [], []}, {==})),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb,
      SCon{cc, SCon{dd, post ++ "\""}}}}}}), Lex.Lex{Lex.Str{}, [], []})), Lex.finish(Lex.run(String.to_list(SCon{'\\',
      SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post ++ "\""}}}}}}), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
      String.to_list(pre), []), []})), [Lex.TStr{pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)}, post}}],
      Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u',
      SCon{aa, SCon{bb, SCon{cc, SCon{dd, post ++ "\""}}}}}}), Lex.Lex{Lex.Str{}, [], []}),
      Lex.run(String.to_list(SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post ++ "\""}}}}}}),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []}),
    M8.seq(pre, SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post ++ "\""}}}}}}, Lex.Lex{Lex.Str{}, [], []},
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []}, M8.lex_raw(String.to_list(pre), h_p,
          [],
      []))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc,
      SCon{dd, post ++ "\""}}}}}}), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(pre), []), []})),
      Lex.finish(Lex.run(String.to_list(post ++ "\""), Lex.Lex{Lex.Str{}, Chr{D2.hex4(aa, bb, cc,
      dd)} <> List.reverse.go(&2, Char, String.to_list(pre), []), []})), [Lex.TStr{pre ++ SCon{Chr{D2.hex4(aa, bb,
      cc, dd)}, post}}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(Lex.run(String.to_list(post ++ "\""),
      zz)), Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char,
      String.to_list(pre), []), []})))),
    Lex.Lex{Lex.Str{}, Chr{D2.hex4(aa, bb, cc, dd)} <> List.reverse.go(&2, Char, String.to_list(pre), []), []},
      Equal.trans(Lex.Lex, Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0},
      List.reverse.go(&2, Char, String.to_list(pre), []), []})))), Lex.unicode.end(D2.hex4(aa, bb, cc, dd),
      List.reverse.go(&2, Char, String.to_list(pre), []), []), Lex.Lex{Lex.Str{}, Chr{D2.hex4(aa, bb, cc,
      dd)} <> List.reverse.go(&2, Char, String.to_list(pre), []), []},
    M3.u4_feed(aa, bb, cc, dd, List.reverse.go(&2, Char, String.to_list(pre), []), M3.and4_1(D2.hexd(aa), D2.hexd(bb),
      D2.hexd(cc), D2.hexd(dd), h_h), M3.and4_2(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), h_h),
      M3.and4_3(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), h_h), M3.and4_4(D2.hexd(aa), D2.hexd(bb),
      D2.hexd(cc), D2.hexd(dd), h_h)),
    Equal.cong(Lex.Sur, Lex.Lex, zz => Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char,
      String.to_list(pre), []), [], zz), Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)), Lex.SOk{},
      M3.sur_ok(D2.hex4(aa, bb, cc, dd), h_n)))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(post ++ "\""), Lex.Lex{Lex.Str{},
      Chr{D2.hex4(aa, bb, cc, dd)} <> List.reverse.go(&2, Char, String.to_list(pre), []), []})),
      Lex.finish(Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(post),
      Chr{D2.hex4(aa, bb, cc, dd)} <> List.reverse.go(&2, Char, String.to_list(pre), [])), []})),
      [Lex.TStr{pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)}, post}}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
      zz => Lex.finish(zz), Lex.run(String.to_list(post ++ "\""), Lex.Lex{Lex.Str{}, Chr{D2.hex4(aa, bb, cc,
      dd)} <> List.reverse.go(&2, Char, String.to_list(pre), []), []}), Lex.run(String.to_list("\""),
      Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(post), Chr{D2.hex4(aa, bb, cc,
      dd)} <> List.reverse.go(&2, Char, String.to_list(pre), [])), []}),
    M8.seq(post, "\"", Lex.Lex{Lex.Str{}, Chr{D2.hex4(aa, bb, cc, dd)} <> List.reverse.go(&2, Char, String.to_list(pre),
      []), []}, Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char, String.to_list(post), Chr{D2.hex4(aa, bb, cc,
      dd)} <> List.reverse.go(&2, Char, String.to_list(pre), [])), []}, M8.lex_raw(String.to_list(post), h_q,
      Chr{D2.hex4(aa, bb, cc, dd)} <> List.reverse.go(&2, Char, String.to_list(pre), []), []))),
    Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TStr{zz}], Lex.text(List.reverse.go(&2, Char,
      String.to_list(post), Chr{D2.hex4(aa, bb, cc, dd)} <> List.reverse.go(&2, Char, String.to_list(pre), []))),
      pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)}, post}, esc_text(pre, Chr{D2.hex4(aa, bb, cc, dd)}, post))))))

def Laws.esc_u(pre, aa, bb, cc, dd, post, h_p, h_h, h_n, h_q, h_s):
  M8.one_str(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post}}}}}} ++ "\""),
    pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)}, post}, Equal.trans(List<&2, Lex.Tok>,
    M5.dens(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, post}}}}}} ++ "\"")),
    M5.dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
    post}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [], []}))),
    [Lex.TStr{pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)}, post}}], M2.lexers_agree("\"" ++ pre ++ SCon{'\\', SCon{'u',
      SCon{aa, SCon{bb, SCon{cc, SCon{dd, post}}}}}} ++ "\"", h_s),
    Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M5.dens(zz),
      Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
      post}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [], []})), [Lex.TStr{pre ++ SCon{Chr{D2.hex4(aa, bb, cc, dd)}, post}}],
      esc_u_lex(pre, aa, bb, cc, dd, post, h_p, h_h, h_n, h_q))))

# the character lexer on a string with a surrogate pair
law esc_pair_lex:
  for +pre: String
  for +h1: Char
  for +h2: Char
  for +h3: Char
  for +h4: Char
  for +l1: Char
  for +l2: Char
  for +l3: Char
  for +l4: Char
  for +post: String
  for +h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  for +h_h: {Bool.and(D2.hexd(h1), Bool.and(D2.hexd(h2), Bool.and(D2.hexd(h3), D2.hexd(h4)))) == True{} : Bool}
  for +h_l: {Bool.and(D2.hexd(l1), Bool.and(D2.hexd(l2), Bool.and(D2.hexd(l3), D2.hexd(l4)))) == True{} : Bool}
  for +h_hi: {D2.in_hi(D2.hex4(h1, h2, h3, h4)) == True{} : Bool}
  for +h_lo: {D2.lo_sur(D2.hex4(l1, l2, l3, l4)) == True{} : Bool}
  for +h_q: {D1.raw_ok(String.to_list(post)) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\',
    SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [],
    []})) == [Lex.TStr{pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))},
    post}}] : List<&2, Lex.Tok>}

def esc_pair_lex(pre, h1, h2, h3, h4, l1, l2, l3, l4, post, h_p, h_h, h_l, h_hi, h_lo, h_q):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1,
    SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\""),
    Lex.Lex{Lex.Idle{}, [], []})), Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2,
    SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}),
    Lex.Lex{Lex.Str{}, [], []})), [Lex.TStr{pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3,
    l4))}, post}}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz),
    Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
    SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [], []}),
    Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
    SCon{l1, SCon{l2, SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}), Lex.Lex{Lex.Str{}, [], []}),
    M8.seq("\"", pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2,
      SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}, Lex.Lex{Lex.Idle{}, [], []}, Lex.Lex{Lex.Str{}, [], []}, {==})),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2,
      SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}),
      Lex.Lex{Lex.Str{}, [], []})), Lex.finish(Lex.run(String.to_list(SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3,
      SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}), Lex.Lex{Lex.Str{},
      List.reverse.go(&2, Char, String.to_list(pre), []), []})), [Lex.TStr{pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2,
      h3, h4), D2.hex4(l1, l2, l3, l4))}, post}}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz),
      Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
      SCon{l1, SCon{l2, SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}), Lex.Lex{Lex.Str{}, [], []}),
      Lex.run(String.to_list(SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1,
      SCon{l2, SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
      String.to_list(pre), []), []}),
    M8.seq(pre, SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3,
      SCon{l4, post ++ "\""}}}}}}}}}}}}, Lex.Lex{Lex.Str{}, [], []}, Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
      String.to_list(pre), []), []}, M8.lex_raw(String.to_list(pre), h_p, [], []))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3,
      SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post ++ "\""}}}}}}}}}}}}), Lex.Lex{Lex.Str{},
      List.reverse.go(&2, Char, String.to_list(pre), []), []})), Lex.finish(Lex.run(String.to_list(post ++ "\""),
      Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2,
      Char, String.to_list(pre), []), []})), [Lex.TStr{pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4),
      D2.hex4(l1, l2, l3, l4))}, post}}], Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
      zz => Lex.finish(Lex.run(String.to_list(post ++ "\""), zz)), Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1,
      Lex.feed('u', Lex.feed('\\', Lex.feed(h4, Lex.feed(h3, Lex.feed(h2, Lex.feed(h1, Lex.Lex{Lex.Uni{3n, 0},
      List.reverse.go(&2, Char, String.to_list(pre), []), []})))))))))),
    Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2,
      Char, String.to_list(pre), []), []}, Equal.trans(Lex.Lex, Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1,
      Lex.feed('u', Lex.feed('\\', Lex.feed(h4, Lex.feed(h3, Lex.feed(h2, Lex.feed(h1, Lex.Lex{Lex.Uni{3n, 0},
      List.reverse.go(&2, Char, String.to_list(pre), []), []})))))))))), Lex.feed(l4, Lex.feed(l3, Lex.feed(l2,
      Lex.feed(l1, Lex.feed('u', Lex.feed('\\', Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)}, List.reverse.go(&2, Char,
      String.to_list(pre), []), []})))))), Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1,
      l2, l3, l4))} <> List.reverse.go(&2, Char, String.to_list(pre), []), []}, Equal.cong(Lex.Lex, Lex.Lex,
      zz => Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.feed('u', Lex.feed('\\', zz)))))),
    Lex.feed(h4, Lex.feed(h3, Lex.feed(h2, Lex.feed(h1, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char,
      String.to_list(pre), []), []})))), Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)}, List.reverse.go(&2, Char,
      String.to_list(pre), []), []},
    Equal.trans(Lex.Lex, Lex.feed(h4, Lex.feed(h3, Lex.feed(h2, Lex.feed(h1, Lex.Lex{Lex.Uni{3n, 0},
      List.reverse.go(&2, Char, String.to_list(pre), []), []})))), Lex.unicode.end(D2.hex4(h1, h2, h3, h4),
      List.reverse.go(&2, Char, String.to_list(pre), []), []), Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)},
      List.reverse.go(&2, Char, String.to_list(pre), []), []}, M3.u4_feed(h1, h2, h3, h4, List.reverse.go(&2, Char,
      String.to_list(pre), []), M3.and4_1(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3), D2.hexd(h4), h_h),
      M3.and4_2(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3), D2.hexd(h4), h_h), M3.and4_3(D2.hexd(h1), D2.hexd(h2),
      D2.hexd(h3), D2.hexd(h4), h_h), M3.and4_4(D2.hexd(h1), D2.hexd(h2), D2.hexd(h3), D2.hexd(h4), h_h)),
      Equal.cong(Lex.Sur, Lex.Lex, zz => Lex.unicode.end.go(D2.hex4(h1, h2, h3, h4), List.reverse.go(&2, Char,
        String.to_list(pre), []), [], zz), Lex.unicode.sur(D2.hex4(h1, h2, h3, h4)), Lex.SHi{}, M3.sur_hi(D2.hex4(h1,
        h2, h3, h4), h_hi)))),
    Equal.trans(Lex.Lex, Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.feed('u', Lex.feed('\\',
      Lex.Lex{Lex.Hi{D2.hex4(h1, h2, h3, h4)}, List.reverse.go(&2, Char, String.to_list(pre), []), []})))))),
      Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.Lex{Lex.Lo{3n, 0, D2.hex4(h1, h2, h3, h4)},
      List.reverse.go(&2, Char, String.to_list(pre), []), []})))), Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2,
      h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2, Char, String.to_list(pre), []), []}, {==},
    Equal.trans(Lex.Lex, Lex.feed(l4, Lex.feed(l3, Lex.feed(l2, Lex.feed(l1, Lex.Lex{Lex.Lo{3n, 0, D2.hex4(h1, h2,
      h3, h4)}, List.reverse.go(&2, Char, String.to_list(pre), []), []})))), Lex.unicode.low.end(D2.hex4(l1, l2, l3,
      l4), D2.hex4(h1, h2, h3, h4), List.reverse.go(&2, Char, String.to_list(pre), []), []), Lex.Lex{Lex.Str{},
      Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2, Char,
      String.to_list(pre), []), []}, M3.l4_feed(l1, l2, l3, l4, D2.hex4(h1, h2, h3, h4), List.reverse.go(&2, Char,
      String.to_list(pre), []), M3.and4_1(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), h_l),
      M3.and4_2(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), h_l), M3.and4_3(D2.hexd(l1), D2.hexd(l2),
      D2.hexd(l3), D2.hexd(l4), h_l), M3.and4_4(D2.hexd(l1), D2.hexd(l2), D2.hexd(l3), D2.hexd(l4), h_l)),
    Equal.cong(Lex.Sur, Lex.Lex, zz => Lex.unicode.low.end.go(D2.hex4(l1, l2, l3, l4), D2.hex4(h1, h2, h3, h4),
      List.reverse.go(&2, Char, String.to_list(pre), []), [], zz), Lex.unicode.sur(D2.hex4(l1, l2, l3, l4)),
      Lex.SLo{},
    M3.sur_lo(D2.hex4(l1, l2, l3, l4), h_lo)))))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(post ++ "\""), Lex.Lex{Lex.Str{},
      Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2, Char,
      String.to_list(pre), []), []})), Lex.finish(Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, List.reverse.go(&2,
      Char, String.to_list(post), Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3,
      l4))} <> List.reverse.go(&2, Char, String.to_list(pre), [])), []})),
      [Lex.TStr{pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))}, post}}],
      Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list(post ++ "\""),
      Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2,
      Char, String.to_list(pre), []), []}), Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
      String.to_list(post), Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2,
      Char, String.to_list(pre), [])), []}),
    M8.seq(post, "\"", Lex.Lex{Lex.Str{}, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3,
      l4))} <> List.reverse.go(&2, Char, String.to_list(pre), []), []}, Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
      String.to_list(post), Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2,
      Char, String.to_list(pre), [])), []}, M8.lex_raw(String.to_list(post), h_q, Chr{D1.pair(D2.hex4(h1, h2, h3, h4),
      D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2, Char, String.to_list(pre), []), []))),
    Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TStr{zz}], Lex.text(List.reverse.go(&2, Char,
      String.to_list(post), Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))} <> List.reverse.go(&2,
      Char, String.to_list(pre), []))), pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3,
      l4))}, post}, esc_text(pre, Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))}, post))))))

def Laws.esc_pair(pre, h1, h2, h3, h4, l1, l2, l3, l4, post, h_p, h_h, h_l, h_hi, h_lo, h_q, h_s):
  M8.one_str(Lex.tokens("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
    SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\""), pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4),
    D2.hex4(l1, l2, l3, l4))}, post}, Equal.trans(List<&2, Lex.Tok>, M5.dens(Lex.tokens("\"" ++ pre ++ SCon{'\\',
    SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4,
    post}}}}}}}}}}}} ++ "\"")), M5.dens(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1,
    SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\""),
    Lex.Lex{Lex.Idle{}, [], []}))),
    [Lex.TStr{pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))}, post}}],
      M2.lexers_agree("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4, SCon{'\\', SCon{'u',
      SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\"", h_s),
    Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M5.dens(zz),
      Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{h1, SCon{h2, SCon{h3, SCon{h4,
      SCon{'\\', SCon{'u', SCon{l1, SCon{l2, SCon{l3, SCon{l4, post}}}}}}}}}}}} ++ "\""), Lex.Lex{Lex.Idle{}, [],
      []})), [Lex.TStr{pre ++ SCon{Chr{D1.pair(D2.hex4(h1, h2, h3, h4), D2.hex4(l1, l2, l3, l4))}, post}}],
      esc_pair_lex(pre, h1, h2, h3, h4, l1, l2, l3, l4, post, h_p, h_h, h_l, h_hi, h_lo, h_q))))

# the rejecting lexer rejects whatever follows
law rej_bad:
  for +cs: List<&2, Char>
  M4.rj(Lex.run(cs, Lex.Lex{Lex.Bad{}, [], []}))

def rej_bad(cs):
  Equal.cong(Lex.Lex, Bool, zz => M4.has_bad(Lex.finish(zz)), Lex.run(cs, Lex.Lex{Lex.Bad{}, [], []}),
      Lex.Lex{Lex.Bad{},
    [], []}, M6.bad_run(cs))

# whether a \u code point is a low surrogate
def is_slo(k: Lex.Sur) -> Bool:
  match k:
    case Lex.SOk{}:
      False{}
    case Lex.SHi{}:
      False{}
    case Lex.SLo{}:
      True{}

# the low half of lo_key
law lo_key.lo:
  for g2: Bool
  for l2: Bool
  for h: {Bool.and(g2, l2) == False{} : Bool}
  {is_slo(Lex.unicode.sur.lo(g2, l2)) == False{} : Bool}

def lo_key.lo(g2, l2, h):
  match g2 l2:
    case True{} True{}:
      Empty.absurd({is_slo(Lex.unicode.sur.lo(True{}, True{})) == False{} : Bool}, M1.true_false(h))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# lo_key, with the high range tests named
law lo_key.go:
  for g1: Bool
  for l1: Bool
  for +cp: U32
  for h: {Bool.and(Bool.not(Bool.and(g1, l1)), D2.in_lo(cp)) == False{} : Bool}
  {is_slo(Lex.unicode.sur.hi(cp, g1, l1)) == False{} : Bool}

def lo_key.go(g1, l1, cp, h):
  match g1 l1:
    case True{} True{}:
      {==}
    case True{} False{}:
      lo_key.lo(U32.is_ge(cp, 56320), U32.is_le(cp, 57343), h)
    case False{} True{}:
      lo_key.lo(U32.is_ge(cp, 56320), U32.is_le(cp, 57343), h)
    case False{} False{}:
      lo_key.lo(U32.is_ge(cp, 56320), U32.is_le(cp, 57343), h)

# a code point that is no low surrogate is not read as one
law lo_key:
  for +cp: U32
  for h: {D2.lo_sur(cp) == False{} : Bool}
  {is_slo(Lex.unicode.sur(cp)) == False{} : Bool}

def lo_key(cp, h):
  lo_key.go(U32.is_ge(cp, 55296), U32.is_le(cp, 56319), cp, h)

# a second \u escape after a high surrogate that is no low surrogate
law low_end_bad:
  for k: Lex.Sur
  for +lo: U32
  for +hi: U32
  for +bf: List<&2, Char>
  for h: {is_slo(k) == False{} : Bool}
  {Lex.unicode.low.end.go(lo, hi, bf, [], k) == Lex.Lex{Lex.Bad{}, [], []} : Lex.Lex}

def low_end_bad(k, lo, hi, bf, h):
  match k:
    case Lex.SOk{}:
      {==}
    case Lex.SHi{}:
      {==}
    case Lex.SLo{}:
      Empty.absurd({Lex.unicode.low.end.go(lo, hi, bf, [], Lex.SLo{}) == Lex.Lex{Lex.Bad{}, [], []} : Lex.Lex},
        M1.true_false(h))

# a \u escape's last digit, when there is a character for it
law uni_rej.z:
  for ok: Bool
  for +acc: U32
  for +hd: Char
  for +tl: List<&2, Char>
  for +bf: List<&2, Char>
  for e: {D2.hexd(hd) == ok : Bool}
  for h: {Bool.and(ok, True{}) == False{} : Bool}
  M4.rj(Lex.run(hd <> tl, Lex.Lex{Lex.Uni{0n, acc}, bf, []}))

def uni_rej.z(ok, acc, hd, tl, bf, e, h):
  match ok:
    case True{}:
      Empty.absurd(M4.rj(Lex.run(hd <> tl, Lex.Lex{Lex.Uni{0n, acc}, bf, []})), M1.true_false(h))
    case False{}:
      es = Equal.sym(Bool, D2.hexd(hd), False{}, e)
      %es : M4.rj(Lex.run(tl, Lex.unicode.go(0n, acc, hd, bf, [], _)))
      rej_bad(tl)

# a \u escape's digit before its last, when there is a character for it
law uni_rej.s:
  for ok: Bool
  for +p: Nat
  for +acc: U32
  for +hd: Char
  for +tl: List<&2, Char>
  for +bf: List<&2, Char>
  for e: {D2.hexd(hd) == ok : Bool}
  for h: {Bool.and(ok, Laws.hexn(1n+p, tl)) == False{} : Bool}
  for ih: {Laws.hexn(1n+p, tl) == False{} : Bool} -> M4.rj(Lex.run(tl, Lex.Lex{Lex.Uni{p, D2.hex.acc(acc, hd)}, bf,
      []}))
  M4.rj(Lex.run(hd <> tl, Lex.Lex{Lex.Uni{1n+p, acc}, bf, []}))

def uni_rej.s(ok, p, acc, hd, tl, bf, e, h, ih):
  match ok:
    case True{}:
      es = Equal.sym(Bool, D2.hexd(hd), True{}, e)
      %es : M4.rj(Lex.run(tl, Lex.unicode.go(1n+p, acc, hd, bf, [], _)))
      ih(h)
    case False{}:
      es = Equal.sym(Bool, D2.hexd(hd), False{}, e)
      %es : M4.rj(Lex.run(tl, Lex.unicode.go(1n+p, acc, hd, bf, [], _)))
      rej_bad(tl)

# a \u escape whose digits run short is rejected
law uni_rej:
  for cs: List<&2, Char>
  for left: Nat
  for +acc: U32
  for +bf: List<&2, Char>
  for h: {Laws.hexn(1n+left, cs) == False{} : Bool}
  M4.rj(Lex.run(cs, Lex.Lex{Lex.Uni{left, acc}, bf, []}))

def uni_rej(cs, left, acc, bf, h):
  match cs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      match left:
        case 0n:
          uni_rej.z(D2.hexd(hd), acc, hd, tl, bf, {==}, h)
        case 1n+(+p):
          uni_rej.s(D2.hexd(hd), p, acc, hd, tl, bf, {==}, h, xx => uni_rej(tl, p, D2.hex.acc(acc, hd), bf, xx))

# a low surrogate escape's last digit, when there is a character for it
law lo_rej.z:
  for ok: Bool
  for +acc: U32
  for +hi: U32
  for +hd: Char
  for +tl: List<&2, Char>
  for +bf: List<&2, Char>
  for e: {D2.hexd(hd) == ok : Bool}
  for h: {Bool.and(ok, D2.lo_sur(D2.hex.acc(acc, hd))) == False{} : Bool}
  M4.rj(Lex.run(hd <> tl, Lex.Lex{Lex.Lo{0n, acc, hi}, bf, []}))

def lo_rej.z(ok, acc, hi, hd, tl, bf, e, h):
  match ok:
    case True{}:
      es = Equal.sym(Bool, D2.hexd(hd), True{}, e)
      %es : M4.rj(Lex.run(tl, Lex.unicode.low.go(0n, acc, hi, hd, bf, [], _)))
      Equal.trans(Bool, M4.has_bad(Lex.finish(Lex.run(tl, Lex.unicode.low.end.go(D2.hex.acc(acc, hd), hi, bf, [],
        Lex.unicode.sur(D2.hex.acc(acc, hd)))))), M4.has_bad(Lex.finish(Lex.run(tl, Lex.Lex{Lex.Bad{}, [], []}))),
        True{}, Equal.cong(Lex.Lex, Bool, zz => M4.has_bad(Lex.finish(Lex.run(tl, zz))),
        Lex.unicode.low.end.go(D2.hex.acc(acc, hd), hi, bf, [], Lex.unicode.sur(D2.hex.acc(acc, hd))),
        Lex.Lex{Lex.Bad{}, [], []}, low_end_bad(Lex.unicode.sur(D2.hex.acc(acc, hd)), D2.hex.acc(acc, hd), hi, bf,
        lo_key(D2.hex.acc(acc, hd), h))), rej_bad(tl))
    case False{}:
      es = Equal.sym(Bool, D2.hexd(hd), False{}, e)
      %es : M4.rj(Lex.run(tl, Lex.unicode.low.go(0n, acc, hi, hd, bf, [], _)))
      rej_bad(tl)

# a low surrogate escape's digit before its last, when there is a character
# for it
law lo_rej.s:
  for ok: Bool
  for +p: Nat
  for +acc: U32
  for +hi: U32
  for +hd: Char
  for +tl: List<&2, Char>
  for +bf: List<&2, Char>
  for e: {D2.hexd(hd) == ok : Bool}
  for h: {Bool.and(ok, Laws.lo_tail(tl, p, D2.hex.acc(acc, hd))) == False{} : Bool}
  for ih: {Laws.lo_tail(tl, p, D2.hex.acc(acc, hd)) == False{} : Bool} -> M4.rj(Lex.run(tl, Lex.Lex{Lex.Lo{p,
    D2.hex.acc(acc, hd), hi}, bf, []}))
  M4.rj(Lex.run(hd <> tl, Lex.Lex{Lex.Lo{1n+p, acc, hi}, bf, []}))

def lo_rej.s(ok, p, acc, hi, hd, tl, bf, e, h, ih):
  match ok:
    case True{}:
      es = Equal.sym(Bool, D2.hexd(hd), True{}, e)
      %es : M4.rj(Lex.run(tl, Lex.unicode.low.go(1n+p, acc, hi, hd, bf, [], _)))
      ih(h)
    case False{}:
      es = Equal.sym(Bool, D2.hexd(hd), False{}, e)
      %es : M4.rj(Lex.run(tl, Lex.unicode.low.go(1n+p, acc, hi, hd, bf, [], _)))
      rej_bad(tl)

# a second \u escape after a high surrogate that is no low surrogate's is
# rejected
law lo_rej:
  for cs: List<&2, Char>
  for left: Nat
  for +acc: U32
  for +hi: U32
  for +bf: List<&2, Char>
  for h: {Laws.lo_tail(cs, left, acc) == False{} : Bool}
  M4.rj(Lex.run(cs, Lex.Lex{Lex.Lo{left, acc, hi}, bf, []}))

def lo_rej(cs, left, acc, hi, bf, h):
  match cs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      match left:
        case 0n:
          lo_rej.z(D2.hexd(hd), acc, hi, hd, tl, bf, {==}, h)
        case 1n+(+p):
          lo_rej.s(D2.hexd(hd), p, acc, hi, hd, tl, bf, {==}, h, xx => lo_rej(tl, p, D2.hex.acc(acc, hd), hi, bf,
            xx))

# the character after a high surrogate escape's backslash
law hiesc_rej.a:
  for ok: Bool
  for +hd: Char
  for +tl: List<&2, Char>
  for +hi: U32
  for +bf: List<&2, Char>
  for e: {D1.is_cp(hd, 117) == ok : Bool}
  for h: {Bool.and(ok, Laws.lo_tail(tl, 3n, 0)) == False{} : Bool}
  M4.rj(Lex.run(hd <> tl, Lex.Lex{Lex.HiEsc{hi}, bf, []}))

def hiesc_rej.a(ok, hd, tl, hi, bf, e, h):
  match ok:
    case True{}:
      es = Equal.sym(Bool, D1.is_cp(hd, 117), True{}, e)
      %es : M4.rj(Lex.run(tl, Lex.step.hiesc.go(hi, bf, [], _)))
      lo_rej(tl, 3n, 0, hi, bf, h)
    case False{}:
      es = Equal.sym(Bool, D1.is_cp(hd, 117), False{}, e)
      %es : M4.rj(Lex.run(tl, Lex.step.hiesc.go(hi, bf, [], _)))
      rej_bad(tl)

# after a high surrogate escape's backslash, no u and low surrogate
law hiesc_rej:
  for cs: List<&2, Char>
  for +hi: U32
  for +bf: List<&2, Char>
  for h: {Laws.lo_next.u(cs) == False{} : Bool}
  M4.rj(Lex.run(cs, Lex.Lex{Lex.HiEsc{hi}, bf, []}))

def hiesc_rej(cs, hi, bf, h):
  match cs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      hiesc_rej.a(D1.is_cp(hd, 117), hd, tl, hi, bf, {==}, h)

# the character after a high surrogate escape
law hi_rej.a:
  for ok: Bool
  for +hd: Char
  for +tl: List<&2, Char>
  for +hi: U32
  for +bf: List<&2, Char>
  for e: {D1.is_cp(hd, 92) == ok : Bool}
  for h: {Bool.and(ok, Laws.lo_next.u(tl)) == False{} : Bool}
  M4.rj(Lex.run(hd <> tl, Lex.Lex{Lex.Hi{hi}, bf, []}))

def hi_rej.a(ok, hd, tl, hi, bf, e, h):
  match ok:
    case True{}:
      es = Equal.sym(Bool, D1.is_cp(hd, 92), True{}, e)
      %es : M4.rj(Lex.run(tl, Lex.step.hi.go(hi, bf, [], _)))
      hiesc_rej(tl, hi, bf, h)
    case False{}:
      es = Equal.sym(Bool, D1.is_cp(hd, 92), False{}, e)
      %es : M4.rj(Lex.run(tl, Lex.step.hi.go(hi, bf, [], _)))
      rej_bad(tl)

# a high surrogate escape with no low surrogate escape after it is rejected
law hi_rej:
  for cs: List<&2, Char>
  for +hi: U32
  for +bf: List<&2, Char>
  for h: {Laws.lo_next(cs) == False{} : Bool}
  M4.rj(Lex.run(cs, Lex.Lex{Lex.Hi{hi}, bf, []}))

def hi_rej(cs, hi, bf, h):
  match cs:
    case Nil{}:
      {==}
    case +hd <> +tl:
      hi_rej.a(D1.is_cp(hd, 92), hd, tl, hi, bf, {==}, h)

# a string's opening quote, raw characters and \u
law pre_u:
  for +pre: String
  for +rest: String
  for +h_p: {D1.raw_ok(String.to_list(pre)) == True{} : Bool}
  {Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}), Lex.Lex{Lex.Idle{}, [],
    []}) == Lex.run(String.to_list(rest), Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []),
    []}) : Lex.Lex}

def pre_u(pre, rest, h_p):
  Equal.trans(Lex.Lex, Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}), Lex.Lex{Lex.Idle{}, [],
    []}), Lex.run(String.to_list(pre ++ SCon{'\\', SCon{'u', rest}}), Lex.Lex{Lex.Str{}, [], []}),
    Lex.run(String.to_list(rest), Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []), []}),
    M8.seq("\"", pre ++ SCon{'\\', SCon{'u', rest}}, Lex.Lex{Lex.Idle{}, [], []}, Lex.Lex{Lex.Str{}, [], []}, {==}),
    M8.seq(pre, SCon{'\\', SCon{'u', rest}}, Lex.Lex{Lex.Str{}, [], []}, Lex.Lex{Lex.Str{}, List.reverse.go(&2, Char,
    String.to_list(pre), []), []}, M8.lex_raw(String.to_list(pre), h_p, [], [])))

def Laws.esc_u_bad(pre, rest, h_p, h_x, h_s):
  M4.lex_none("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}, h_s, Equal.trans(Bool,
    M4.has_bad(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}), Lex.Lex{Lex.Idle{}, [],
    []}))), M4.has_bad(Lex.finish(Lex.run(String.to_list(rest), Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char,
    String.to_list(pre), []), []}))), True{}, Equal.cong(Lex.Lex, Bool, zz => M4.has_bad(Lex.finish(zz)),
    Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', rest}}), Lex.Lex{Lex.Idle{}, [], []}),
    Lex.run(String.to_list(rest), Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []), []}),
    pre_u(pre, rest, h_p)), uni_rej(String.to_list(rest), 3n, 0, List.reverse.go(&2, Char, String.to_list(pre), []),
    h_x)))

def Laws.esc_lo_bad(pre, aa, bb, cc, dd, rest, h_p, h_h, h_lo, h_s):
  M4.lex_none("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}, h_s, Equal.trans(Bool,
    M4.has_bad(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
    rest}}}}}}), Lex.Lex{Lex.Idle{}, [], []}))), M4.has_bad(Lex.finish(Lex.run(String.to_list(rest), Lex.feed(dd,
    Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []),
    []}))))))), True{}, Equal.cong(Lex.Lex, Bool, zz => M4.has_bad(Lex.finish(zz)),
    Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}),
    Lex.Lex{Lex.Idle{}, [], []}), Lex.run(String.to_list(rest), Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa,
    Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []), []}))))), pre_u(pre, SCon{aa, SCon{bb,
    SCon{cc, SCon{dd, rest}}}}, h_p)), Equal.trans(Bool, M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
        Lex.feed(dd,
    Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []),
    []}))))))), M4.has_bad(Lex.finish(Lex.run(String.to_list(rest), Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd),
    List.reverse.go(&2, Char, String.to_list(pre), []), [], Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)))))), True{},
    Equal.cong(Lex.Lex, Bool, zz => M4.has_bad(Lex.finish(Lex.run(String.to_list(rest), zz))), Lex.feed(dd, Lex.feed(cc,
    Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []), []})))),
    Lex.unicode.end(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), []), M3.u4_feed(aa, bb,
    cc, dd, List.reverse.go(&2, Char, String.to_list(pre), []), M3.and4_1(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc),
    D2.hexd(dd), h_h), M3.and4_2(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), h_h), M3.and4_3(D2.hexd(aa),
    D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), h_h), M3.and4_4(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc),
    D2.hexd(dd), h_h))), Equal.trans(Bool, M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
    Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), [],
    Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)))))), M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
    Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), [],
    Lex.SLo{})))), True{}, Equal.cong(Lex.Sur, Bool, zz => M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
    Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), [], zz)))),
    Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)), Lex.SLo{}, M3.sur_lo(D2.hex4(aa, bb, cc, dd), h_lo)),
    rej_bad(String.to_list(rest))))))

def Laws.esc_hi_bad(pre, aa, bb, cc, dd, rest, h_p, h_h, h_hi, h_n, h_s):
  M4.lex_none("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}, h_s, Equal.trans(Bool,
    M4.has_bad(Lex.finish(Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd,
    rest}}}}}}), Lex.Lex{Lex.Idle{}, [], []}))), M4.has_bad(Lex.finish(Lex.run(String.to_list(rest), Lex.feed(dd,
    Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []),
    []}))))))), True{}, Equal.cong(Lex.Lex, Bool, zz => M4.has_bad(Lex.finish(zz)),
    Lex.run(String.to_list("\"" ++ pre ++ SCon{'\\', SCon{'u', SCon{aa, SCon{bb, SCon{cc, SCon{dd, rest}}}}}}),
    Lex.Lex{Lex.Idle{}, [], []}), Lex.run(String.to_list(rest), Lex.feed(dd, Lex.feed(cc, Lex.feed(bb, Lex.feed(aa,
    Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []), []}))))), pre_u(pre, SCon{aa, SCon{bb,
    SCon{cc, SCon{dd, rest}}}}, h_p)), Equal.trans(Bool, M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
        Lex.feed(dd,
    Lex.feed(cc, Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []),
    []}))))))), M4.has_bad(Lex.finish(Lex.run(String.to_list(rest), Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd),
    List.reverse.go(&2, Char, String.to_list(pre), []), [], Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)))))), True{},
    Equal.cong(Lex.Lex, Bool, zz => M4.has_bad(Lex.finish(Lex.run(String.to_list(rest), zz))), Lex.feed(dd, Lex.feed(cc,
    Lex.feed(bb, Lex.feed(aa, Lex.Lex{Lex.Uni{3n, 0}, List.reverse.go(&2, Char, String.to_list(pre), []), []})))),
    Lex.unicode.end(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), []), M3.u4_feed(aa, bb,
    cc, dd, List.reverse.go(&2, Char, String.to_list(pre), []), M3.and4_1(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc),
    D2.hexd(dd), h_h), M3.and4_2(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), h_h), M3.and4_3(D2.hexd(aa),
    D2.hexd(bb), D2.hexd(cc), D2.hexd(dd), h_h), M3.and4_4(D2.hexd(aa), D2.hexd(bb), D2.hexd(cc),
    D2.hexd(dd), h_h))), Equal.trans(Bool, M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
    Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), [],
    Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)))))), M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
    Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), [],
    Lex.SHi{})))), True{}, Equal.cong(Lex.Sur, Bool, zz => M4.has_bad(Lex.finish(Lex.run(String.to_list(rest),
    Lex.unicode.end.go(D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), [], zz)))),
    Lex.unicode.sur(D2.hex4(aa, bb, cc, dd)), Lex.SHi{}, M3.sur_hi(D2.hex4(aa, bb, cc, dd), h_hi)),
    hi_rej(String.to_list(rest), D2.hex4(aa, bb, cc, dd), List.reverse.go(&2, Char, String.to_list(pre), []), h_n)))))
