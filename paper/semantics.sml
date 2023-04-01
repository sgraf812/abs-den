(* This file needs a SML of New Jersey distribution *)

type name = string
type addr = int
datatype expr = VAR of name | APP of expr * name | LAM of name * expr | LET of name * expr * expr
type value = expr

datatype cont = STOP | APPLY of addr * cont | UPDATE of addr * cont
structure Env = BinaryMapFn(struct type ord_key = string; val compare = String.compare; end)
type env = addr Env.map
structure Heap = IntRedBlackMap
type 'd heap' = (expr * env * 'd) Heap.map
datatype control = EVAL of expr | RET of value * semv
and state = S of control * env * semd heap' * cont
and trace = END of state | CONS of state * (unit -> trace)
and semd = D of state -> trace
and semv = FUN of addr -> semd
type heap = semd heap'

exception Undefined
fun undef () = raise Undefined
fun eq_expr (c1 : expr) (c2 : expr) = true (* ommitted *)
fun eq_ctrl (c1 : control) (c2 : control) = true (* ommitted *)
fun eq_state (s1 : state) (s2 : state) = true (* ommitted *)
fun src (END(s))    = s
  | src (CONS(s,_)) = s
fun tgt (END(s))    = s
  | tgt (CONS(_,t)) = tgt (t ())
fun concat (END(s))     f  = let val t = f () in if eq_state s (src t) then t else undef () end
  | concat (CONS(s,f1)) f2 = CONS(s,fn () => concat (f1 ()) f2)
fun stay s = END(s)
fun comp (D(d1)) (D(d2)) = D(fn s => let val t1 = d1 s in concat t1 (fn () => d2 (tgt t1)) end)
fun >>>(d1,d2) = comp d1 d2
infixr 5 >>>

exception Stay
fun at c1 c2 = if eq_ctrl c1 c2 then () else raise Stay
fun at_expr e1 e2 = if eq_expr e1 e2 then () else raise Stay
fun step f = D (fn s => CONS(s,f s) handle Stay => END(s))
fun val_ (v, semv) (S(c,e,h,k)) () = (at (EVAL(v)) c; END(S(RET(v,semv),e,h,k)))
fun look (e as VAR(x)) (S(c,env,heap,k)) =
  let val _ = at (EVAL(e)) c
      val a = Env.lookup(env,x) handle NotFound => raise Stay
      val (e,env',D(d)) = Heap.lookup(heap,a) handle NotFound => raise Stay
  in
    fn () => d(S(EVAL(e),env',heap,UPDATE(a,k)))
  end
fun upd (S(c,env,heap,k)) =
  let val (v,semv) = case c of RET(v,semv) => (v,semv) | _ => raise Stay
      val (a,k') = case k of UPDATE(a,k') => (a,k') | _ => raise Stay
      val heap' = Heap.insert(heap,a,(v,env,step(val_(v,semv))))
  in
    fn () => END(S(RET(v,semv),env,heap',k'))
  end
fun app1 (e as APP(e',x)) (S(c,env,heap,k)) =
  let val _ = at (EVAL(e)) c
      val a = Env.lookup(env,x) handle NotFound => raise Stay
  in
    fn () => END(S(EVAL(e'),env,heap,APPLY(a,k)))
  end
fun app2 (e as LAM(x,e'), a) (S(c,env,heap,k)) =
  let val (v,semv) = case c of RET(v,semv as FUN(_)) => (v,semv) | _ => raise Stay
      val _ = at_expr e v
      val (a,k') = case k of APPLY(a,k') => (a,k') | _ => raise Stay
  in
    fn () => END(S(EVAL(e'),Env.insert(env,x,a),heap,k'))
  end
fun let_ d1 (S(c,env,heap,k)) =
  let val (x,e1,e2) = case c of EVAL(LET(x,e1,e2)) => (x,e1,e2) | _ => raise Stay
      val a = Heap.numItems heap
      val env' = Env.insert(env,x,a)
      val heap' = Heap.insert(heap,a,(e1,env',d1))
  in
    fn () => END(S(EVAL(e2),env',heap',k))
  end
val apply = D (fn s => case s of
  S(RET(_,FUN(f)),_,_,APPLY(a,_)) => (case f a of D d => d s)
  | _                             => END(s))

fun ask (f : state -> semd) : semd = D (fn s => case f s of D d => d s)
fun sem (e : expr) : semd = ask (fn s as S(c,_,_,_) =>
  (at (EVAL(e)) c; case e of
    VAR(x) => step(look(e)) >>> step(upd)
    | LAM(x,e') => let fun f a = step(app2(e,a)) >>> sem e'
                   in step(val_(e,FUN(f))) end
    | APP(e',x) => step(app1(e)) >>> sem e' >>> apply
    | LET(x,e1,e2) => step(let_(sem(e1))) >>> sem e2))

fun take 0 t = END(src t)
  | take n (END(s)) = END(s)
  | take n (CONS(s,f)) = CONS(s,fn () => take (n-1) (f ()))
fun toList (END(s)) = [s]
  | toList (CONS(s,f)) = s :: toList (f ())
fun run n e = toList (take n (case sem e of D(d) => d(S(EVAL(e),Env.empty,Heap.empty,STOP))))

(* Parser *)

structure P = ParserComb

val +> = P.seq
infixr 3 +>

fun skipWS getc = P.skipBefore Char.isSpace getc

fun nameParser getc = P.bind(P.seqWith String.^ (
      P.wrap (P.eatChar Char.isAlpha, str),
      P.wrap (P.option (P.token Char.isAlphaNum), fn s => case s of SOME(s') => s' | NONE => "")),
      fn s => if s = "let" orelse s = "in" then P.failure else P.result s) getc;
fun varParser getc = P.wrap(nameParser, VAR) getc
fun letParser getc = P.wrap (
      P.string "let" +> skipWS(nameParser) +> skipWS(P.char #"=") +> expParser
      +> skipWS(P.string "in") +> expParser,
      fn (_, (x, (_, (e1, (_, e2))))) => LET(x, e1, e2)) getc
and lamParser getc = P.wrap (
      P.string "λ" +> skipWS(nameParser) +> skipWS(P.char #".") +> expParser,
      fn (_, (x, (_, e))) => LAM(x,e)) getc
and expParser getc = P.wrap (
      skipWS (P.seq (
         P.or' [letParser, lamParser, varParser],
         appParser)),
      fn (e, es) => List.foldl (fn (a, b) => APP(b, a)) e es) getc
and appParser getc =
      P.zeroOrMore (skipWS nameParser) getc

exception NoParse of string
fun read s = case StringCvt.scanString expParser s of SOME(e) => e | NONE => raise NoParse(s);
val e1 = read "x"
val e2 = read "x y"
val e3 = read "λx.x"
val e4 = read "let id = λx.x in id id"
val e5 = read "let x = x in x"
val e6 = read "let f = λy.y y in f f"
val e7 = read " let id = λa. let y = a in y in \
              \ let z = λc.c in \
              \ let d = id id in \
              \ let e = id z in \
              \ d e d"
;
(* Tests *)
Control.Print.printDepth := 1000;
val ts = map (run 10) [e1,e2,e3,e4,e5,e6,e7]
val t = run 30 e7
