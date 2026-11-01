# a derivation's text, regrouped in front of a tail
import Base
import ../../laws/defs/GrammarDerivations.bend as D1
import ./ArrayLength.bend as M1
import ./CursorFollowsDerivation.bend as M2

# an append regrouped, then its right side rewritten
law app3:
  for +aa: String
  for +bb: String
  for +tail: String
  for +mid: String
  for +rhs: String
  for e1: {bb ++ tail == mid : String}
  for e2: {aa ++ mid == rhs : String}
  {(aa ++ bb) ++ tail == rhs : String}

def app3(aa, bb, tail, mid, rhs, e1, e2):
  Equal.trans(String, (aa ++ bb) ++ tail, aa ++ (bb ++ tail), rhs, M2.sassoc(aa, bb, tail),
    Equal.trans(String, aa ++ (bb ++ tail), aa ++ mid, rhs,
      Equal.cong(String, String, xx => aa ++ xx, bb ++ tail, mid, e1), e2))

# spelled pieces then a tail are sp
law sp_eq:
  for +ps: List<&2, D1.Piece>
  for +tail: String
  {D1.spell(ps) ++ tail == M1.sp(ps, tail) : String}

def sp_eq(ps, tail):
  match ps:
    case Nil{}:
      {==}
    case +pc <> +tl:
      app3(D1.piece.text(pc), D1.spell(tl), tail, M1.sp(tl, tail), D1.piece.text(pc) ++ M1.sp(tl, tail),
        sp_eq(tl, tail), {==})

# a derivation's text in front of a tail, grouped to the right
def gt(gg: D1.Gv, tail: String) -> String:
  match gg:
    case D1.GWord{w}:
      w ++ tail
    case D1.GStr{ps}:
      SCon{'"', M1.sp(ps, SCon{'"', tail})}
    case D1.GArr0{w0}:
      SCon{'[', w0 ++ SCon{']', tail}}
    case D1.GArr{w0, vv, w1, rr}:
      SCon{'[', w0 ++ gt(vv, w1 ++ gt(rr, SCon{']', tail}))}
    case D1.GObj0{w0}:
      SCon{'{', w0 ++ SCon{'}', tail}}
    case D1.GObj{w0, ps, w1, w2, vv, w3, rr}:
      SCon{'{', w0 ++ SCon{'"', M1.sp(ps, SCon{'"', w1 ++ SCon{':', w2 ++ gt(vv, w3 ++ gt(rr, SCon{'}', tail}))}})}}
    case D1.GEnd{}:
      tail
    case D1.GNext{w2, vv, w1, rr}:
      SCon{',', w2 ++ gt(vv, w1 ++ gt(rr, tail))}
    case D1.GNextM{w4, ps, w1, w2, vv, w3, rr}:
      SCon{',', w4 ++ SCon{'"', M1.sp(ps, SCon{'"', w1 ++ SCon{':', w2 ++ gt(vv, w3 ++ gt(rr, tail))}})}}

# a member's text after its name's opening quote, in front of a tail
law mem_eq:
  for +ps: List<&2, D1.Piece>
  for +w1: String
  for +w2: String
  for +vv: D1.Gv
  for +w3: String
  for +rs: String
  for +rt: String
  for +tail: String
  for +ev: {D1.g.text(vv) ++ (w3 ++ rt) == gt(vv, w3 ++ rt) : String}
  for +er: {rs ++ tail == rt : String}
  {(D1.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ rs) ++ tail
    == M1.sp(ps, SCon{'"', w1 ++ SCon{':', w2 ++ gt(vv, w3 ++ rt)}}) : String}

def mem_eq(ps, w1, w2, vv, w3, rs, rt, tail, ev, er):
  +t3 = w3 ++ rt
  +t2 = w2 ++ gt(vv, t3)
  +t1 = w1 ++ SCon{':', t2}
  app3(D1.spell(ps), "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ rs, tail, SCon{'"', t1},
    M1.sp(ps, SCon{'"', t1}),
    Equal.cong(String, String, xx => SCon{'"', xx}, (w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ rs) ++ tail,
      t1,
      app3(w1, ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ rs, tail, SCon{':', t2}, t1,
        Equal.cong(String, String, xx => SCon{':', xx}, (w2 ++ D1.g.text(vv) ++ w3 ++ rs) ++ tail, t2,
          app3(w2, D1.g.text(vv) ++ w3 ++ rs, tail, gt(vv, t3), t2,
            app3(D1.g.text(vv), w3 ++ rs, tail, t3, gt(vv, t3),
              app3(w3, rs, tail, rt, t3, er, {==}), ev), {==})), {==})),
    sp_eq(ps, SCon{'"', t1}))

# a derivation's text then a tail is gt
law gt_eq:
  for +gg: D1.Gv
  for +tail: String
  {D1.g.text(gg) ++ tail == gt(gg, tail) : String}

def gt_eq(gg, tail):
  match gg:
    case D1.GWord{_}:
      {==}
    case D1.GStr{+ps}:
      Equal.cong(String, String, xx => SCon{'"', xx}, (D1.spell(ps) ++ "\"") ++ tail, M1.sp(ps, SCon{'"', tail}),
        app3(D1.spell(ps), "\"", tail, SCon{'"', tail}, M1.sp(ps, SCon{'"', tail}), {==}, sp_eq(ps, SCon{'"', tail})))
    case D1.GArr0{+w0}:
      Equal.cong(String, String, xx => SCon{'[', xx}, (w0 ++ "]") ++ tail, w0 ++ SCon{']', tail},
        app3(w0, "]", tail, SCon{']', tail}, w0 ++ SCon{']', tail}, {==}, {==}))
    case D1.GArr{+w0, +vv, +w1, +rr}:
      +t1 = w1 ++ gt(rr, SCon{']', tail})
      Equal.cong(String, String, xx => SCon{'[', xx}, (w0 ++ D1.g.text(vv) ++ w1 ++ D1.g.text(rr) ++ "]") ++ tail,
        w0 ++ gt(vv, t1),
        app3(w0, D1.g.text(vv) ++ w1 ++ D1.g.text(rr) ++ "]", tail, gt(vv, t1), w0 ++ gt(vv, t1),
          app3(D1.g.text(vv), w1 ++ D1.g.text(rr) ++ "]", tail, t1, gt(vv, t1),
            app3(w1, D1.g.text(rr) ++ "]", tail, gt(rr, SCon{']', tail}), t1,
              app3(D1.g.text(rr), "]", tail, SCon{']', tail}, gt(rr, SCon{']', tail}), {==},
                gt_eq(rr, SCon{']', tail})), {==}),
            gt_eq(vv, t1)), {==}))
    case D1.GObj0{+w0}:
      Equal.cong(String, String, xx => SCon{'{', xx}, (w0 ++ "}") ++ tail, w0 ++ SCon{'}', tail},
        app3(w0, "}", tail, SCon{'}', tail}, w0 ++ SCon{'}', tail}, {==}, {==}))
    case D1.GObj{+w0, +ps, +w1, +w2, +vv, +w3, +rr}:
      +t3 = w3 ++ gt(rr, SCon{'}', tail})
      +t1 = "\"" ++ M1.sp(ps, SCon{'"', w1 ++ SCon{':', w2 ++ gt(vv, t3)}})
      Equal.cong(String, String, xx => SCon{'{', xx},
        (w0 ++ "\"" ++ D1.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ D1.g.text(rr) ++ "}")
          ++ tail, w0 ++ t1,
        app3(w0, "\"" ++ D1.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ D1.g.text(rr) ++ "}",
          tail, t1, w0 ++ t1,
          Equal.cong(String, String, xx => SCon{'"', xx},
            (D1.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ D1.g.text(rr) ++ "}") ++ tail,
            M1.sp(ps, SCon{'"', w1 ++ SCon{':', w2 ++ gt(vv, t3)}}),
            mem_eq(ps, w1, w2, vv, w3, D1.g.text(rr) ++ "}", gt(rr, SCon{'}', tail}), tail, gt_eq(vv, t3),
              app3(D1.g.text(rr), "}", tail, SCon{'}', tail}, gt(rr, SCon{'}', tail}), {==},
                gt_eq(rr, SCon{'}', tail})))), {==}))
    case D1.GEnd{}:
      {==}
    case D1.GNext{+w2, +vv, +w1, +rr}:
      +t1 = w1 ++ gt(rr, tail)
      Equal.cong(String, String, xx => SCon{',', xx}, (w2 ++ D1.g.text(vv) ++ w1 ++ D1.g.text(rr)) ++ tail,
        w2 ++ gt(vv, t1),
        app3(w2, D1.g.text(vv) ++ w1 ++ D1.g.text(rr), tail, gt(vv, t1), w2 ++ gt(vv, t1),
          app3(D1.g.text(vv), w1 ++ D1.g.text(rr), tail, t1, gt(vv, t1),
            app3(w1, D1.g.text(rr), tail, gt(rr, tail), t1, gt_eq(rr, tail), {==}),
            gt_eq(vv, t1)), {==}))
    case D1.GNextM{+w4, +ps, +w1, +w2, +vv, +w3, +rr}:
      +t3 = w3 ++ gt(rr, tail)
      +t1 = "\"" ++ M1.sp(ps, SCon{'"', w1 ++ SCon{':', w2 ++ gt(vv, t3)}})
      Equal.cong(String, String, xx => SCon{',', xx},
        (w4 ++ "\"" ++ D1.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ D1.g.text(rr)) ++ tail,
        w4 ++ t1,
        app3(w4, "\"" ++ D1.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ D1.g.text(rr),
          tail, t1, w4 ++ t1,
          Equal.cong(String, String, xx => SCon{'"', xx},
            (D1.spell(ps) ++ "\"" ++ w1 ++ ":" ++ w2 ++ D1.g.text(vv) ++ w3 ++ D1.g.text(rr)) ++ tail,
            M1.sp(ps, SCon{'"', w1 ++ SCon{':', w2 ++ gt(vv, t3)}}),
            mem_eq(ps, w1, w2, vv, w3, D1.g.text(rr), gt(rr, tail), tail, gt_eq(vv, t3), gt_eq(rr, tail))), {==}))
