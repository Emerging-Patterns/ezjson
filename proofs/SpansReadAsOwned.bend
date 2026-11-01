# proofs of laws/SpansReadAsOwned.bend
import Base
import ../src/value.bend as V
import ../src/lazy.bend as Lazy
import ../laws/SpansReadAsOwned.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/KeySearch.bend as M1

# at.go's early exit, owned
law at_own.at:
  for zz: Bool
  for +hd: V.Json
  for +tl: V.Json
  for +idx: U32
  for ih: {D1.own(V.at.go(tl, U32.sub(idx, 1))) == V.at.go(D1.own(tl), U32.sub(idx, 1)) : V.Json}
  {D1.own(Lazy.stop(V.Json, zz, hd, _u => V.at.go(tl, U32.sub(idx, 1)))) ==
    Lazy.stop(V.Json, zz, D1.own(hd), _u => V.at.go(D1.own(tl), U32.sub(idx, 1))) : V.Json}

def at_own.at(zz, _hd, _tl, _idx, ih):
  match zz:
    case True{}:
      {==}
    case False{}:
      ih

# an index search, owned
law at_own:
  for +cells: V.Json
  for +idx: U32
  {D1.own(V.at.go(cells, idx)) == V.at.go(D1.own(cells), idx) : V.Json}

def at_own(cells, idx):
  match cells:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      at_own.at(U32.is_zero(idx), x1, x2, idx, at_own(x2, U32.sub(idx, 1)))
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

def Laws.at_same(val, idx):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      at_own(x1, idx)
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

def Laws.as_str_same(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

def Laws.as_bool_same(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

def Laws.as_num_same(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

def Laws.as_u32_same(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}

def Laws.as_f32_same(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{+x1}:
      {==}
    case V.JNum{+x1}:
      {==}
    case V.JStr{+x1}:
      {==}
    case V.JArr{+x1}:
      {==}
    case V.JObj{+x1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+x1, +x2}:
      {==}
    case V.JPair{+x1, +x2, +x3}:
      {==}
    case V.JSpan{+x1, +x2}:
      {==}
    case V.JBind{+x1, +x2, +x3, +x4}:
      {==}
