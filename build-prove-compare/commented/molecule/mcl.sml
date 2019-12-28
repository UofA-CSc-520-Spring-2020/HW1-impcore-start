(* <mcl.sml>=                                   *)
exception Unimp of string
fun unimp s = raise Unimp s


(*****************************************************************)
(*                                                               *)
(*   EXCEPTIONS USED IN LANGUAGES WITH TYPE CHECKING             *)
(*                                                               *)
(*****************************************************************)

(* All interpreters that include type checkers  *)
(* incorporate this code:                       *)
(* <exceptions used in languages with type checking>= *)
exception TypeError of string
exception BugInTypeChecking of string


(*****************************************************************)
(*                                                               *)
(*   \FOOTNOTESIZE SHARED: NAMES, ENVIRONMENTS, STRINGS, ERRORS, PRINTING, INTERACTION, STREAMS, \&\ INITIALIZATION *)
(*                                                               *)
(*****************************************************************)

(* Each interpreter that is written in ML incorporates *)
(* all the following code chunks, some of which are *)
(* defined in \crefmlscheme.chap and some of which are *)
(* defined below.                               *)
(* <\footnotesize shared: names, environments, strings, errors, printing, interaction, streams, \&\ initialization>= *)
(* <for working with curried functions: [[id]], [[fst]], [[snd]], [[pair]], [[curry]], and [[curry3]]>= *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* There are a variety of ways to create useful *)
(* functions in the [[f]] position. Many such functions *)
(* are Curried. Here are some of them.          *)
(* <boxed values 238>=                          *)
val _ = op fst    : ('a * 'b) -> 'a
val _ = op snd    : ('a * 'b) -> 'b
val _ = op pair   : 'a -> 'b -> 'a * 'b
val _ = op curry  : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
val _ = op curry3 : ('a * 'b * 'c -> 'd) -> ('a -> 'b -> 'c -> 'd)
(* <support for names and environments>=        *)
type name = string
(* The [[type]] syntax here is like C's [[typedef]], it *)
(* defines a type by type abbreviation.         *)

(* <support for names and environments>=        *)
type 'a env = (name * 'a) list
val emptyEnv = []

(* lookup and check of existing bindings *)
exception NotFound of name
fun find (name, []) = raise NotFound name
  | find (name, (n, v)::tail) = if name = n then v else find (name, tail)

(* composition *)
infix 6 <+>
fun pairs <+> pairs' = pairs' @ pairs

(* adding new bindings *)
exception BindListLength
fun bind (name, v, rho) = (name, v) :: rho
fun bindList (n::vars, v::vals, rho) = bindList (vars, vals, bind (n, v, rho))
  | bindList ([], [], rho) = rho
  | bindList _ = raise BindListLength

fun mkEnv (xs, vs) = bindList (xs, vs, emptyEnv)

(* In the code, function [[find]] is closely related to *)
(* the [[find]] from \crefscheme.chap: it returns *)
(* whatever is in the environment, which has type [['a]] *)
(* and not type [[Value *]]. But [[bind]] and   *)
(* [[bindList]] are more loosely related to \cref *)
(* scheme.chap's [[bindalloc]] and [[bindalloclist]]: *)
(* although the ML versions add bindings, they do not *)
(* allocate. \stdbreak (The phrases in the box are *)
(* adapted from declarations that appear in the *)
(* interfaces to ML modules; through some Noweb hackery, *)
(* the declarations are checked by the ML compiler.) \ *)
(* mlsflabelbindList,find,bind \mlslabelenv     *)
(* <boxed values 1>=                            *)
val _ = op emptyEnv : 'a env
val _ = op find     : name * 'a env -> 'a
val _ = op bind     : name      * 'a      * 'a env -> 'a env
val _ = op bindList : name list * 'a list * 'a env -> 'a env
(* <support for names and environments>=        *)
fun duplicatename [] = NONE
  | duplicatename (x::xs) =
      if List.exists (fn x' => x' = x) xs then
        SOME x
      else
        duplicatename xs
(* <boxed values 19>=                           *)
val _ = op duplicatename : name list -> name option
(* <support for names and environments>=        *)
fun extend (rho, bindings) =
  foldr (fn ((x, a), rho) => bind (x, a, rho)) rho bindings
(* Extension is an operation we also see in \xlet forms, *)
(* but this is the first interpreter in which I write it *)
(* as a function. \umlflabelextend              *)
(* <boxed values 101>=                          *)
val _ = op extend : 'a env * 'a env -> 'a env
(* The [[xdeftable]] is shared with the Impcore parser. *)
(* Function [[reduce_to_xdef]] is almost shareable as *)
(* well, but not quite---the abstract syntax of *)
(* [[DEFINE]] is different.                     *)

(* <support for names and environments>=        *)
exception DisjointUnionFailed of name
fun disjointUnion envs =
  let val env = List.concat envs
  in  case duplicatename (map fst env)
        of NONE => env
         | SOME x => raise DisjointUnionFailed x
  end
(* Function [[disjointUnion]] combines environments and *)
(* checks for duplicate names. If it finds a duplicate *)
(* name, it raises [[DisjointUnionFailed]]. This *)
(* exception can be raised only during type inference, *)
(* not during evaluation.                       *)
(* <boxed values 102>=                          *)
val _ = op disjointUnion : 'a env list -> 'a env
(* The [[xdeftable]] is shared with the Impcore parser. *)
(* Function [[reduce_to_xdef]] is almost shareable as *)
(* well, but not quite---the abstract syntax of *)
(* [[DEFINE]] is different.                     *)

(* <support for names and environments>=        *)
fun isbound (x, E) = (find (x, E); true) handle NotFound _ => false
(* Error detection and signaling                *)
(*                                              *)
(* Every run-time error is signaled by raising the *)
(* [[RuntimeError]] exception, which carries an error *)
(* message.                                     *)
(* <support for detecting and signaling errors detected at run time>= *)
exception RuntimeError of string (* error message *)
(* <support for detecting and signaling errors detected at run time>= *)
fun errorIfDups (what, xs, context) =
  case duplicatename xs
    of NONE   => ()
     | SOME x => raise RuntimeError (what ^ " " ^ x ^ " appears twice in " ^
                                                                        context)
(* Function [[errorIfDups]] raises the exception if a *)
(* duplicate name is found. Parameter [[what]] says what *)
(* kind of name we're looking at, and [[context]] says *)
(* in what context.                             *)
(* <boxed values 20>=                           *)
val _ = op errorIfDups : string * name list * string -> unit
(* Some errors might be caused not by a fault in *)
(* micro-Scheme code but in my implementation of *)
(* micro-Scheme. For those times, there's the   *)
(* [[InternalError]] exception.                 *)
(* <support for detecting and signaling errors detected at run time>= *)
exception InternalError of string (* bug in the interpreter *)
(* <list functions not provided by \sml's initial basis>= *)
fun zip3 ([], [], []) = []
  | zip3 (x::xs, y::ys, z::zs) = (x, y, z) :: zip3 (xs, ys, zs)
  | zip3 _ = raise ListPair.UnequalLengths

fun unzip3 [] = ([], [], [])
  | unzip3 (trip::trips) =
      let val (x,  y,  z)  = trip
          val (xs, ys, zs) = unzip3 trips
      in  (x::xs, y::ys, z::zs)
      end
(* Standard ML's list-reversal function is called *)
(* [[rev]], but in this book I use [[reverse]]. *)
(* <list functions not provided by \sml's initial basis>= *)
val reverse = rev
(* <list functions not provided by \sml's initial basis>= *)
fun optionList [] = SOME []
  | optionList (NONE :: _) = NONE
  | optionList (SOME x :: rest) =
      (case optionList rest
         of SOME xs => SOME (x :: xs)
          | NONE    => NONE)
(* Reusable utility functions                   *)
(*                                              *)
(* This section includes small utility functions for *)
(* printing, for manipulating automatically generated *)
(* names, and for manipulating sets.            *)
(*                                              *)
(* Utility functions for printing               *)
(*                                              *)
(* For writing values and other information to standard *)
(* output, Standard ML provides a simple [[print]] *)
(* primitive, which writes a string. Anything more *)
(* sophisticated, such as writing to standard error, *)
(* requires using the the [[TextIO]] module, which is *)
(* roughly analogous to C's [[<stdio.h>]]. Using *)
(* [[TextIO]] can be awkward, so I define three *)
(* convenience functions. Function [[println]] is like *)
(* [[print]], but writes a string followed by a newline. *)
(* Functions [[eprint]] and [[eprintln]] are analogous *)
(* to [[print]] and [[println]], but they write to *)
(* standard error. It would be nice to be able to define *)
(* more sophisticated printing functions like the ones *)
(* in \secrefsec:print-interface on page [->], but *)
(* making such functions type-safe requires code that *)
(* beginning ML programmers would find baffling. *)
(* <utility functions for string manipulation and printing>= *)
fun println  s = (print s; print "\n")
fun eprint   s = TextIO.output (TextIO.stdErr, s)
fun eprintln s = (eprint s; eprint "\n")
(* CLOSING IN ON CHECK-PRINT:                   *)
(* <utility functions for string manipulation and printing>= *)
val xprinter = ref print
fun xprint   s = !xprinter s
fun xprintln s = (xprint s; xprint "\n")
(* <utility functions for string manipulation and printing>= *)
fun tryFinally f x post =
  (f x handle e => (post (); raise e)) before post ()

fun withXprinter xp f x =
  let val oxp = !xprinter
      val ()  = xprinter := xp
  in  tryFinally f x (fn () => xprinter := oxp)
  end
(* <utility functions for string manipulation and printing>= *)
fun bprinter () =
  let val buffer = ref []
      fun bprint s = buffer := s :: !buffer
      fun contents () = concat (rev (!buffer))
  in  (bprint, contents)
  end
(* <utility functions for string manipulation and printing>= *)
fun predefinedFunctionError s = eprintln ("while reading predefined functions, "
                                                                            ^ s)
(* <utility functions for string manipulation and printing>= *)
fun intString n =
  String.map (fn #"~" => #"-" | c => c) (Int.toString n)
(* Plurals!                                     *)
(* <utility functions for string manipulation and printing>= *)
fun plural what [x] = what
  | plural what _   = what ^ "s"

fun countString xs what =
  intString (length xs) ^ " " ^ plural what xs
(* <utility functions for string manipulation and printing>= *)
fun separate (zero, sep) = 
  (* list with separator *)
  let fun s []     = zero
        | s [x]    = x
        | s (h::t) = h ^ sep ^ s t
  in  s
end
val spaceSep = separate ("", " ")   (* list separated by spaces *)
val commaSep = separate ("", ", ")  (* list separated by commas *)
(* Standard ML's built-in support for converting *)
(* integers to strings uses the [[ ]] character as a *)
(* minus sign. We want the hyphen.              *)
(* <boxed values 197>=                          *)
val _ = op intString : int -> string
(* Lists! Functions [[spaceSep]] and [[commaSep]] are *)
(* special cases of the more general function   *)
(* [[separate]].                                *)
(* <boxed values 197>=                          *)
val _ = op spaceSep :                    string list -> string
val _ = op commaSep :                    string list -> string
val _ = op separate : string * string -> string list -> string
(* <utility functions for string manipulation and printing>= *)
fun printUTF8 code =
  let val w = Word.fromInt code
      val (&, >>) = (Word.andb, Word.>>)
      infix 6 & >>
      val _ = if (w & 0wx1fffff) <> w then
                raise RuntimeError (intString code ^
                                    " does not represent a Unicode code point")
              else
                 ()
      val printbyte = xprint o str o chr o Word.toInt
      fun prefix byte byte' = Word.orb (byte, byte')
  in  if w > 0wxffff then
        app printbyte [ prefix 0wxf0  (w >> 0w18)
                      , prefix 0wx80 ((w >> 0w12) & 0wx3f)
                      , prefix 0wx80 ((w >>  0w6) & 0wx3f)
                      , prefix 0wx80 ((w      ) & 0wx3f)
                      ]
      else if w > 0wx7ff then
        app printbyte [ prefix 0wxe0  (w >> 0w12)
                      , prefix 0wx80 ((w >>  0w6) & 0wx3f)
                      , prefix 0wx80 ((w        ) & 0wx3f)
                      ]
      else if w > 0wx7f then
        app printbyte [ prefix 0wxc0  (w >>  0w6)
                      , prefix 0wx80 ((w        ) & 0wx3f)
                      ]
      else
        printbyte w
  end
(* <utility functions for string manipulation and printing>= *)
fun fnvHash s =
  let val offset_basis = 0wx011C9DC5 : Word.word  (* trim the high bit *)
      val fnv_prime    = 0w16777619  : Word.word
      fun update (c, hash) = Word.xorb (hash, Word.fromInt (ord c)) * fnv_prime
      fun int w = Word.toIntX w handle Overflow => Word.toInt (Word.andb (w,
                                                                     0wxffffff))
  in  int (foldl update offset_basis (explode s))
  end
(* To hash strings, I use an algorithm by Glenn Fowler, *)
(* Phong Vo, and Landon Curt Noll. The ``offset basis'' *)
(* has been adjusted by removing the high bit, so the *)
(* computation works using 31-bit integers. \urlhttp:// *)
(* tools.ietf.org/html/draft-eastlake-fnv-03 \urlhttp:// *)
(* www.isthe.com/chongo/tech/comp/fnv/          *)
(* <boxed values 198>=                          *)
val _ = op fnvHash : string -> int
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* Utility functions for renaming variables     *)
(*                                              *)
(* In the theory of programming languages, it's fairly *)
(* common to talk about fresh names, where ``fresh'' *)
(* means ``different from any name in the program or its *)
(* environment.'' And if you implement a type checker *)
(* for a polymorphic language like Typed uScheme, or if *)
(* you implement type inference, or if you ever *)
(* implement the lambda calculus, you will need code *)
(* that generates fresh names. \stdbreak You can always *)
(* try names like [[t1]], [[t2]], and so on. But if you *)
(* want to debug, it's usually helpful to relate the *)
(* fresh name to a name already in the program. I like *)
(* to do this by tacking on a numeric suffix; for *)
(* example, to get a fresh name that's like [[x]], *)
(* I might try [[x-1]], [[x-2]], and so on. \stdbreak *)
(* But if the process iterates, I don't want to generate *)
(* a name like [[x-1-1-1]]; I'd much rather generate *)
(* [[x-3]]. This utility function helps by stripping off *)
(* any numeric suffix to recover the original [[x]]. *)
(* <utility functions for string manipulation and printing>= *)
fun stripNumericSuffix s =
      let fun stripPrefix []         = s   (* don't let things get empty *)
            | stripPrefix (#"-"::[]) = s
            | stripPrefix (#"-"::cs) = implode (reverse cs)
            | stripPrefix (c   ::cs) = if Char.isDigit c then stripPrefix cs
                                       else implode (reverse (c::cs))
      in  stripPrefix (reverse (explode s))
      end
(* \stdbreak                                    *)
(*                                              *)
(* Utility functions for sets, collections, and lists *)
(*                                              *)
(* Quite a few analyses of programs, including a type *)
(* checker in \creftypesys.chap and the type inference *)
(* in \crefml.chap, need to manipulate sets of  *)
(* variables. In small programs, such sets are usually *)
(* small, so I provide a simple implementation that *)
(* represents a set using a list with no duplicate *)
(* elements. It's essentially the same implementation *)
(* that you see in micro-Scheme in \crefscheme.chap. [ *)
(* The~\ml~types of the set operations include type *)
(* variables with double primes, like~[[''a]]. The type *)
(* variable~[[''a]] can be instantiated only with an *)
(* ``equality type.'' Equality types include base types *)
(* like strings and integers, as well as user-defined *)
(* types that do not contain functions. Functions \emph *)
(* {cannot} be compared for equality.]          *)

(* Representing error outcomes as values        *)
(*                                              *)
(* When an error occurs, especially during evaluation, *)
(* the best and most convenient thing to do is often to *)
(* raise an ML exception, which can be caught in a *)
(* handler. But it's not always easy to put a handler *)
(* exactly where it's needed to make the control *)
(* transfer work out the way it should. If you need to *)
(* get the code right, sometimes it's better to *)
(* represent an error outcome as a value. Like any other *)
(* value, such a value can be passed and returned until *)
(* it reaches a place where a decision is made. *)
(*                                              *)
(*   • When representing the outcome of a unit test, an *)
(*  error means failure for [[check-expect]] but *)
(*  success for [[check-error]]. Rather than juggle *)
(*  ``exception'' versus ``non-exception,'' I treat *)
(*  both outcomes on the same footing, as values. *)
(*  Successful evaluation to produce bridge-language *)
(*  value v is represented as ML value \monoOK v. *)
(*  Evaluation that signals an error with message m *)
(*  is represented as ML value \monoERROR m.    *)
(*  Constructors [[OK]] and [[ERROR]] are the value *)
(*  constructors of the algebraic data type     *)
(*  [[error]], defined here:                    *)
(* <support for representing errors as \ml\ values>= *)
datatype 'a error = OK of 'a | ERROR of string
(* <support for representing errors as \ml\ values>= *)
infix 1 >>=
fun (OK x)      >>= k  =  k x
  | (ERROR msg) >>= k  =  ERROR msg
(* Sometimes we need to zip together three lists of *)
(* equal length.                                *)
(* <boxed values 202>=                          *)
val _ = op zip3   : 'a list * 'b list * 'c list -> ('a * 'b * 'c) list
val _ = op unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
(* <boxed values 202>=                          *)
val _ = op optionList : 'a option list -> 'a list option
(* What if we have a function [[f]] that could return *)
(* an [['a]] or an error, and another function [[g]] *)
(* that expects an [['a]]? Standard function composition *)
(* and the expression \monoboxg (f x) don't exactly make *)
(* sense, but the idea of composition is good. This form *)
(* of composition poses a standard problem, and it has a *)
(* standard solution. The solution relies on a  *)
(* sequencing operator written [[>>=]], which uses a *)
(* special form of continuation-passing style. (The *)
(* [[>>=]] operator is traditionally called ``bind,'' *)
(* but you might wish to pronounce it ``and then.'') *)
(* The idea is that we apply [[f]] to [[x]], and if the *)
(* result is [[OK y]], we can continue by applying [[g]] *)
(*  to [[y]]. But if the result of applying [[(f x)]] is *)
(* an error, that error is the result of the whole *)
(* computation. The [[>>=]] operator sequences the *)
(* possibly erroneous result [[(f x)]] with the *)
(* continuation [[g]], so where we might wish to write \ *)
(* monoboxg (f x), we instead write             *)
(*                                              *)
(*  [[f x >>= g]].                              *)
(*                                              *)
(* In the definition of [[>>=]], I write the second *)
(* function as [[k]], not [[g]], because [[k]] is *)
(* traditional for a continuation.              *)
(* <boxed values 202>=                          *)
val _ = op >>= : 'a error * ('a -> 'b error) -> 'b error
(* A very common special case occurs when the   *)
(* continuation always succeeds; that is, the   *)
(* continuation [[k']] has type \monobox'a -> 'b instead *)
(* of \monobox'a -> b error. In this case, the execution *)
(* plan is that when [[(f x)]] succeeds, continue by *)
(* applying [[k']] to the result; otherwise propagate *)
(* the error. I know of no standard way to write this *)
(* operator, [Haskell uses [[flip fmap]].] , so I use  *)
(* [[>>=+]], which you might also choose to pronounce *)
(* ``and then.''                                *)

(* <support for representing errors as \ml\ values>= *)
infix 1 >>=+
fun e >>=+ k'  =  e >>= (OK o k')
(* <boxed values 203>=                          *)
val _ = op >>=+ : 'a error * ('a -> 'b) -> 'b error
(* <support for representing errors as \ml\ values>= *)
fun errorList es =
  let fun cons (OK x, OK xs) = OK (x :: xs)
        | cons (ERROR m1, ERROR m2) = ERROR (m1 ^ "; " ^ m2)
        | cons (ERROR m, OK _) = ERROR m
        | cons (OK _, ERROR m) = ERROR m
  in  foldr cons (OK []) es
  end
(* Sometimes we map an error-producing function over a *)
(* list of values to get a list of [['a error]] results. *)
(* Such a list is hard to work with, and the right thing *)
(* to do with it is to convert it to a single value \ *)
(* stdbreak that's either an [['a list]] or an error. *)
(* I call the conversion operation [[errorList]]. [ *)
(* Haskell calls it [[sequence]].] I implement it by *)
(* folding over the list of possibly erroneous results, *)
(* concatenating all error messages.            *)
(* <boxed values 204>=                          *)
val _ = op errorList : 'a error list -> 'a list error
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* Overall interpreter structure                *)
(*                                              *)
(* A reusable read-eval-print loop              *)
(*                                              *)
(* [*] Functions [[eval]] and [[evaldef]] process *)
(* expressions and true definitions. But an interpreter *)
(* for micro-Scheme also has to process the extended *)
(* definitions [[USE]] and [[TEST]], which need more *)
(* tooling:                                     *)
(*                                              *)
(*   • To process a [[USE]], we must be able to parse *)
(*  definitions from a file and enter a         *)
(*  read-eval-print loop recursively.           *)
(*   • To process a [[TEST]] (like [[check_expect]] or *)
(*  [[check_error]]), we must be able to run tests, *)
(*  and to run a test, we must call [[eval]].   *)
(*                                              *)
(* A lot of the tooling can be shared among more than *)
(* one bridge language. To make sharing easy,   *)
(* I introduce some abstraction.                *)
(*                                              *)
(*   • Type [[basis]], which is different for each *)
(*  bridge language, stands for the collection of *)
(*  environment or environments that are used at top *)
(*  level to evaluate a definition. The name basis *)
(*  comes from The Definition of Standard ML \citep *)
(*  milner:definition-revised.                  *)
(*                                              *)
(*  For micro-Scheme, a [[basis]] is a single   *)
(*  environment that maps each name to a mutable *)
(*  location holding a value. For Impcore, a    *)
(*  [[basis]] would include both global-variable and *)
(*  function environments. And for later languages *)
(*  that have static types, a [[basis]] includes *)
(*  environments that store information about types. *)
(*   • Function [[processDef]], which is different for *)
(*  each bridge language, takes a [[def]] and a *)
(*  [[basis]] and returns an updated [[basis]]. *)
(*  For micro-Scheme, [[processDef]] just evaluates *)
(*  the definition, using [[evaldef]]. For languages *)
(*  that have static types (Typed Impcore, Typed *)
(*  uScheme, and \nml in \creftuscheme.chap,ml.chap, *)
(*  among others), [[processDef]] includes two  *)
(*  phases: type checking followed by evaluation. *)
(*                                              *)
(*  Function [[processDef]] also needs to be told *)
(*  about interaction, which has two dimensions: *)
(*  input and output. On input, an interpreter may or *)
(*  may not prompt:                             *)
(* <type [[interactivity]] plus related functions and value>= *)
datatype input_interactivity = PROMPTING | NOT_PROMPTING
(* On output, an interpreter may or may not show a *)
(* response to each definition.                 *)

(* <type [[interactivity]] plus related functions and value>= *)
datatype output_interactivity = PRINTING | NOT_PRINTING
(* <type [[interactivity]] plus related functions and value>= *)
type interactivity = 
  input_interactivity * output_interactivity
val noninteractive = 
  (NOT_PROMPTING, NOT_PRINTING)
fun prompts (PROMPTING,     _) = true
  | prompts (NOT_PROMPTING, _) = false
fun prints (_, PRINTING)     = true
  | prints (_, NOT_PRINTING) = false
(* Both kinds of information go to [[processDef]], as a *)
(* value of type [[interactivity]].             *)
(* <boxed values 21>=                           *)
type interactivity = interactivity
val _ = op noninteractive : interactivity
val _ = op prompts : interactivity -> bool
val _ = op prints  : interactivity -> bool
(* <simple implementations of set operations>=  *)
type 'a set = 'a list
val emptyset = []
fun member x = 
  List.exists (fn y => y = x)
fun insert (x, ys) = 
  if member x ys then ys else x::ys
fun union (xs, ys) = foldl insert ys xs
fun inter (xs, ys) =
  List.filter (fn x => member x ys) xs
fun diff  (xs, ys) = 
  List.filter (fn x => not (member x ys)) xs
(* <boxed values 199>=                          *)
type 'a set = 'a set
val _ = op emptyset : 'a set
val _ = op member   : ''a -> ''a set -> bool
val _ = op insert   : ''a     * ''a set  -> ''a set
val _ = op union    : ''a set * ''a set  -> ''a set
val _ = op inter    : ''a set * ''a set  -> ''a set
val _ = op diff     : ''a set * ''a set  -> ''a set
(* <collections with mapping and combining functions>= *)
datatype 'a collection = C of 'a set
fun elemsC (C xs) = xs
fun singleC x     = C [x]
val emptyC        = C []
(* [*] In the functions above, a set has the same *)
(* representation as a list, and they can be used *)
(* interchangeably. Sometimes, however, the thing you're *)
(* collecting is itself a set, and you want to  *)
(* distinguish (for an example, see \crefpage   *)
(* adt.ex.exhaustiveness). Here is a type [[collection]] *)
(* that is distinct from the set/list type.     *)
(* <boxed values 200>=                          *)
type 'a collection = 'a collection
val _ = op elemsC  : 'a collection -> 'a set
val _ = op singleC : 'a -> 'a collection
val _ = op emptyC  :       'a collection
(* <collections with mapping and combining functions>= *)
fun joinC     (C xs) = C (List.concat (map elemsC xs))
fun mapC  f   (C xs) = C (map f xs)
fun filterC p (C xs) = C (List.filter p xs)
fun mapC2 f (xc, yc) = joinC (mapC (fn x => mapC (fn y => f (x, y)) yc) xc)
(* Function [[mapC2]] is the most powerful of all---its *)
(* type resembles the type of Standard ML's     *)
(* [[ListPair.map]], but it works quite differently: *)
(* where [[ListPair.map]] takes elements pairwise, *)
(* [[mapC2]] takes all possible combinations.   *)
(* In particular, if you give [[ListPair.map]] two lists *)
(* containing N and M elements respectively, \stdbreak *)
(* the number of elements in the result is min(N,M). If *)
(* you give collections of size N and M to [[mapC2]], *)
(* the resulting collection has size N×M.      *)
(* <boxed values 201>=                          *)
val _ = op joinC   : 'a collection collection -> 'a collection
val _ = op mapC    : ('a -> 'b)      -> ('a collection -> 'b collection)
val _ = op filterC : ('a -> bool)    -> ('a collection -> 'a collection)
val _ = op mapC2   : ('a * 'b -> 'c) -> ('a collection * 'b collection -> 'c
                                                                     collection)
(* <suspensions>=                               *)
datatype 'a action
  = PENDING  of unit -> 'a
  | PRODUCED of 'a

type 'a susp = 'a action ref
(* <boxed values 210>=                          *)
type 'a susp = 'a susp
(* <suspensions>=                               *)
fun delay f = ref (PENDING f)
fun demand cell =
  case !cell
    of PENDING f =>  let val result = f ()
                     in  (cell := PRODUCED result; result)
                     end
     | PRODUCED v => v
(* Functions [[delay]] and [[demand]] convert to and *)
(* from suspensions.                            *)
(* <boxed values 211>=                          *)
val _ = op delay  : (unit -> 'a) -> 'a susp
val _ = op demand : 'a susp -> 'a
(* The [[SUSPENDED]] constructor represents a stream in *)
(* which the action need to produce the next element may *)
(* not yet have been taken. \stdbreak Getting the *)
(* element requires demanding a value from a suspension, *)
(* and if the action in the suspension is pending, it is *)
(* performed at that time. [*]                  *)
(* <streams>=                                   *)
datatype 'a stream 
  = EOS
  | :::       of 'a * 'a stream
  | SUSPENDED of 'a stream susp
infixr 3 :::
(* <streams>=                                   *)
fun streamGet EOS = NONE
  | streamGet (x ::: xs)    = SOME (x, xs)
  | streamGet (SUSPENDED s) = streamGet (demand s)
(* <streams>=                                   *)
fun streamOfList xs = 
  foldr (op :::) EOS xs
(* Even though its representation uses mutable state *)
(* (the suspension), the stream is an immutable *)
(* abstraction. [To~help with debugging, I~sometimes *)
(* violate the abstraction and look at the state of a *)
(* [[SUSPENDED]] stream.] To observe that abstraction, *)
(* call [[streamGet]]. This function performs whatever *)
(* actions are needed either to produce a pair holding *)
(* an element an a stream (represented as \monoSOME (x, *)
(* xs) or to decide that the stream is empty and no more *)
(* elements can be produced (represented as [[NONE]]). *)
(* <boxed values 212>=                          *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* The simplest way to create a stream is by using the *)
(* [[:::]] or [[EOS]] constructors. It can also be *)
(* convenient to create a stream from a list. When such *)
(* a stream is read, no new actions are performed. *)
(* <boxed values 212>=                          *)
val _ = op streamOfList : 'a list -> 'a stream
(* <streams>=                                   *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* <streams>=                                   *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* Function [[listOfStream]] creates a list from a *)
(* stream. It is useful for debugging.          *)
(* <boxed values 213>=                          *)
val _ = op listOfStream : 'a stream -> 'a list
(* The more interesting streams are those that result *)
(* from actions. To help create such streams, I define *)
(* [[delayedStream]] as a convenience abbreviation for *)
(* creating a stream from one action.           *)
(* <boxed values 213>=                          *)
val _ = op delayedStream : (unit -> 'a stream) -> 'a stream
(* <streams>=                                   *)
fun streamOfEffects action =
  delayedStream (fn () => case action () of NONE   => EOS
                                          | SOME a => a ::: streamOfEffects
                                                                         action)
(* Creating streams using actions and functions *)
(*                                              *)
(* Function [[streamOfEffects]] produces the stream of *)
(* results obtained by repeatedly performing a single *)
(* action (like reading a line of input). \stdbreak The *)
(* action must have type [[unit -> 'a option]]; the *)
(* stream performs the action repeatedly, producing a *)
(* stream of [['a]] values until performing the action *)
(* returns [[NONE]].                            *)
(* <boxed values 214>=                          *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* I use [[streamOfEffects]] to produce a stream of *)
(* lines from an input file:                    *)

(* <streams>=                                   *)
type line = string
fun filelines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* <boxed values 215>=                          *)
type line = line
val _ = op filelines : TextIO.instream -> line stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <streams>=                                   *)
fun streamRepeat x =
  delayedStream (fn () => x ::: streamRepeat x)
(* Where [[streamOfEffects]] produces the results of *)
(* repeating a single action again and again,   *)
(* [[streamRepeat]] simply repeats a single value again *)
(* and again. This operation might sound useless, but *)
(* here's an example: suppose we read a sequence of *)
(* lines from a file, and for error reporting, we want *)
(* to tag each line with its source location, i.e., file *)
(* name and line number. Well, the file names are all *)
(* the same, and one easy way to associate the same file *)
(* name with every line is to repeat the file name *)
(* indefinitely, then join the two streams using *)
(* [[streamZip]]. Function [[streamRepeat]] creates an *)
(* infinite stream that repeats a value of any type: *)
(* <boxed values 216>=                          *)
val _ = op streamRepeat : 'a -> 'a stream
(* <streams>=                                   *)
fun streamOfUnfold next state =
  delayedStream (fn () => case next state
                            of NONE => EOS
                             | SOME (a, state') => a ::: streamOfUnfold next
                                                                         state')
(* A more sophisticated way to produce a stream is to *)
(* use a function that depends on an evolving state of *)
(* some unknown type [['b]]. The function is applied to *)
(* a state (of type [['b]]) and may produce a pair *)
(* containing a value of type [['a]] and a new state. *)
(* By repeatedly applying the function, we produce a *)
(* sequence of results of type [['a]]. This operation, *)
(* in which a function is used to expand a value into a *)
(* sequence, is the dual of the fold operation, which is *)
(* used to collapse a sequence into a value. The new *)
(* operation is therefore called unfold.        *)
(* <boxed values 217>=                          *)
val _ = op streamOfUnfold : ('b -> ('a * 'b) option) -> 'b -> 'a stream
(* Function [[streamOfUnfold]] can turn any ``get'' *)
(* function into a stream. In fact, the standard unfold *)
(* and get operations should obey the following *)
(* algebraic law:                               *)
(*                                              *)
(*  streamOfUnfold streamGet xs ===xs.          *)
(*                                              *)
(* Another useful ``get'' function is [[(fn n => SOME *)
(* (n, n+1))]]; passing this function to        *)
(* [[streamOfUnfold]] results in an infinite stream of *)
(* increasing integers. [*]                     *)

(* <streams>=                                   *)
val naturals = 
  streamOfUnfold (fn n => SOME (n, n+1)) 0   (* 0 to infinity *)
(* <boxed values 218>=                          *)
val _ = op naturals : int stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* (Streams, like lists, support not only unfolding but *)
(* also folding. Function [[streamFold]] is defined *)
(* below in chunk [->].)                        *)

(* <streams>=                                   *)
fun preStream (pre, xs) = 
  streamOfUnfold (fn xs => (pre (); streamGet xs)) xs
(* It's also useful to be able to perform an action *)
(* immediately after getting an element from a stream. *)
(* In [[postStream]], I perform the action only if *)
(* [[streamGet]] succeeds. By performing the [[post]] *)
(* action only when [[streamGet]] succeeds, I make it *)
(* possible to write a [[post]] action that has access *)
(* to the element just gotten. Post-get actions are *)
(* especially useful for debugging.             *)

(* <streams>=                                   *)
fun postStream (xs, post) =
  streamOfUnfold (fn xs => case streamGet xs
                             of NONE => NONE
                              | head as SOME (x, _) => (post x; head)) xs
(* Given an action called [[pre]] and a stream xs, *)
(* I define a stream \monopreStream (pre, xs) that adds *)
(* [[pre ()]] to the action performed by the stream. *)
(* Roughly speaking,                            *)
(*                                              *)
(*  \monostreamGet (preStream (pre, xs)) = \mono(pre *)
(*  (); streamGet xs).                          *)
(*                                              *)
(* (The equivalence is only rough because the pre action *)
(* is performed lazily, only when an action is needed to *)
(* get a value from xs.)                        *)
(* <boxed values 219>=                          *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <boxed values 219>=                          *)
val _ = op postStream : 'a stream * ('a -> unit) -> 'a stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <streams>=                                   *)
fun streamMap f xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => f x ::: streamMap f xs)
(* <boxed values 220>=                          *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <streams>=                                   *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* <boxed values 221>=                          *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <streams>=                                   *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* The only sensible order in which to fold the elements *)
(* of a stream is the order in which the actions are *)
(* taken and the results are produced: from left to *)
(* right. [*]                                   *)
(* <boxed values 222>=                          *)
val _ = op streamFold : ('a * 'b -> 'b) -> 'b -> 'a stream -> 'b
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <streams>=                                   *)
fun streamZip (xs, ys) =
  delayedStream
  (fn () => case (streamGet xs, streamGet ys)
              of (SOME (x, xs), SOME (y, ys)) => (x, y) ::: streamZip (xs, ys)
               | _ => EOS)
(* <streams>=                                   *)
fun streamConcat xss =
  let fun get (xs, xss) =
        case streamGet xs
          of SOME (x, xs) => SOME (x, (xs, xss))
           | NONE => case streamGet xss
                       of SOME (xs, xss) => get (xs, xss)
                        | NONE => NONE
  in  streamOfUnfold get (EOS, xss)
  end
(* Function [[streamZip]] returns a stream that is as *)
(* long as the shorter of the two argument streams. *)
(* In particular, if [[streamZip]] is applied to a *)
(* finite stream and an infinite stream, the result is a *)
(* finite stream.                               *)
(* <boxed values 223>=                          *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* Concatenation turns a stream of streams of A's into a *)
(* single stream of A's. I define it using a    *)
(* [[streamOfUnfold]] with a two-part state: the first *)
(* element of the state holds an initial [[xs]], and the *)
(* second part holds the stream of all remaining *)
(* streams, [[xss]]. To concatenate the stream of *)
(* streams [[xss]], I use an initial state of [[(EOS, *)
(* xss)]].                                      *)
(* <boxed values 223>=                          *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* <streams>=                                   *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* The composition of [[concat]] with [[map f]] is very *)
(* common in list and stream processing, so I give it a *)
(* name.                                        *)
(* <boxed values 224>=                          *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* <streams>=                                   *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* The code used to append two streams is much like the *)
(* code used to concatenate arbitrarily many streams. *)
(* To avoid duplicating the tricky manipulation of *)
(* states, I simply implement append using      *)
(* concatenation.                               *)
(* <boxed values 225>=                          *)
val _ = op @@@ : 'a stream * 'a stream -> 'a stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <streams>=                                   *)
fun streamTake (0, xs) = []
  | streamTake (n, xs) =
      case streamGet xs
        of SOME (x, xs) => x :: streamTake (n-1, xs)
         | NONE => []
(* Whenever I rename bound variables, for example in a *)
(* type \/\ldotsnalpha\alldottau, I have to choose new *)
(* names that don't conflict with existing names in tau *)
(* or in the environment. The easiest way to get good *)
(* names to build an infinite stream of names by using *)
(* [[streamMap]] on [[naturals]], then use      *)
(* [[streamFilter]] to choose only the good ones, and *)
(* finally to take exactly as many good names as I need *)
(* by calling [[streamTake]], which is defined here. *)
(* <boxed values 226>=                          *)
val _ = op streamTake : int * 'a stream -> 'a list
(* <streams>=                                   *)
fun streamDrop (0, xs) = xs
  | streamDrop (n, xs) =
      case streamGet xs
        of SOME (_, xs) => streamDrop (n-1, xs)
         | NONE => EOS
(* If I want ``take,'' sooner or later I'm sure to want *)
(* ``drop'' (\chunkrefmlinterps.chunk.use-streamDrop). *)
(* <boxed values 227>=                          *)
val _ = op streamDrop : int * 'a stream -> 'a stream
(* <stream transformers and their combinators>= *)
type ('a, 'b) xformer = 
  'a stream -> ('b error * 'a stream) option
(* Stream transformers, which act as parsers    *)
(*                                              *)
(* Our ultimate goal is to turn streams of input lines *)
(* into streams of definitions. Along the way we may *)
(* also have streams of characters, tokens, types, *)
(* expressions, and more. To handle all these different *)
(* kinds of streams using a single set of operators, *)
(* I define a type representing a stream transformer. *)
(* A stream transformer from A to B takes a stream of A *)
(* 's as input and either succeeds, fails, or detects an *)
(* error:                                       *)
(*                                              *)
(*   • If it succeeds, it consumes zero or more A's from *)
(*  the input stream and produces exactly one B. *)
(*  It returns a pair containing [[OK]] B plus  *)
(*  whatever A's were not consumed.             *)
(*   • If it fails, it returns [[NONE]].      *)
(*   • If it detects an error, it returns a pair *)
(*  containing [[ERROR]] m, where m is a message, *)
(*  plus whatever A's were not consumed.        *)
(*                                              *)
(* <boxed values 234>=                          *)
type ('a, 'b) xformer = ('a, 'b) xformer
(* If we apply [[streamOfUnfold]], from \cref   *)
(* mlinterps.streams, to an [[('a, 'b) xformer]], \ *)
(* mdbusemlinterpsstreamOfUnfold we get a function that *)
(* maps a stream of A's to a stream of B's-with-error. *)

(* <stream transformers and their combinators>= *)
fun pure y = fn xs => SOME (OK y, xs)
(* --- #2                                       *)
(* \newskip\myskip \myskip=4pt                  *)
(*                                              *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(* \catcode`=\other \catcode`_=\other \catcode`$=\other *)
(*                                              *)
(*  \toprule Stream transformers;               *)
(*  applying functions to                       *)
(*  transformers                                *)
(*  \midrule \type('a, 'b) xformer              *)
(*  \tableboxpure : 'b -> ('a, 'b)              *)
(*  xformer \splitbox<*>('a, 'b ->              *)
(*  'c) xformer * ('a, 'b)                      *)
(*  xformer-> ('a, 'c) xformer \                *)
(*  tablebox<> : ('b -> 'c) * ('a,              *)
(*  'b) xformer -> ('a, 'c) xformer             *)
(*  \tablebox<>? : ('b -> 'c                    *)
(*  option) * ('a, 'b) xformer ->               *)
(*  ('a, 'c) xformer \splitbox<*>!              *)
(*  ('a, 'b -> 'c error) xformer *              *)
(*  ('a, 'b) xformer-> ('a, 'c)                 *)
(*  xformer \tablebox<>! : ('b ->               *)
(*  'c error) * ('a, 'b) xformer ->             *)
(*  ('a, 'c) xformer [8pt] \midrule             *)
(*  Functions useful with [[<>]]                *)
(*  and [[<*>]]                                 *)
(*  \tableboxfst : ('a * 'b) -> 'a              *)
(*  \tableboxsnd : ('a * 'b) -> 'b              *)
(*  \tableboxpair : 'a -> 'b -> 'a              *)
(*  * 'b \tableboxcurry : ('a * 'b              *)
(*  -> 'c) -> ('a -> 'b -> 'c) \                *)
(*  tableboxcurry3 : ('a * 'b * 'c              *)
(*  -> 'd) -> ('a -> 'b -> 'c ->                *)
(*  'd) [8pt] \midrule Combining                *)
(*  transformers in sequence,                   *)
(*  alternation, or conjunction                 *)
(*  \tablebox<* : ('a, 'b) xformer  >]] : ('a, 'b) *)
(*  * ('a, 'c) xformer -> ('a, 'b)  xformer * ('a, *)
(*  xformer \tablebox *> : ('a, 'b) 'c) xformer -> *)
(*  xformer * ('a, 'c) xformer ->   ('a, 'c) xformer *)
(*  ('a, 'c) xformer \tablebox< :   [8pt] \midrule *)
(*  'b * ('a, 'c) xformer -> ('a,   Transformers *)
(*  'b) xformer \tablebox<|> : ('a, useful for both *)
(*  'b) xformer * ('a, 'b) xformer  lexical analysis *)
(*  -> ('a, 'b) xformer \tablebox   and parsing *)
(*  pzero : ('a, 'b) xformer \                  *)
(*  tableboxanyParser : ('a, 'b)                *)
(*  xformer list -> ('a, 'b)                    *)
(*  xformer \tablebox[[<                        *)
(*  \tableboxone : ('a, 'a) xformer             *)
(*  \tableboxeos : ('a, unit)                   *)
(*  xformer \tableboxsat : ('b ->               *)
(*  bool) -> ('a, 'b) xformer ->                *)
(*  ('a, 'b) xformer \tableboxeqx :             *)
(*  ''b -> ('a, ''b) xformer ->                 *)
(*  ('a, ''b) xformer \tablebox                 *)
(*  notFollowedBy : ('a, 'b)                    *)
(*  xformer -> ('a, unit) xformer \             *)
(*  tableboxmany : ('a, 'b) xformer             *)
(*  -> ('a, 'b list) xformer \                  *)
(*  tableboxmany1 : ('a, 'b)                    *)
(*  xformer -> ('a, 'b list)                    *)
(*  xformer \tableboxoptional :                 *)
(*  ('a, 'b) xformer -> ('a, 'b                 *)
(*  option) xformer \tableboxpeek :             *)
(*  ('a, 'b) xformer -> 'a stream               *)
(*  -> 'b option \tableboxrewind :              *)
(*  ('a, 'b) xformer -> ('a, 'b)                *)
(*  xformer \bottomrule                         *)
(*                                              *)
(* Stream transformers and their combinators [*] *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(*                                              *)
(* Error-free transformers and their composition *)
(*                                              *)
(* The [[pure]] combinator takes a value [[h]] of type B *)
(* as argument. It returns an \atob transformer that *)
(* consumes no A's as input and produces [[y]]. *)
(* <boxed values 235>=                          *)
val _ = op pure : 'b -> ('a, 'b) xformer
(* <stream transformers and their combinators>= *)
infix 3 <*>
fun tx_f <*> tx_b =
  fn xs => case tx_f xs
             of NONE => NONE
              | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
              | SOME (OK f, xs) =>
                  case tx_b xs
                    of NONE => NONE
                     | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
                     | SOME (OK y, xs) => SOME (OK (f y), xs)
(* For the combination [[tx_f <*> tx_b]] to succeed, *)
(* both [[tx_f]] and [[tx_b]] must succeed. Ensuring *)
(* that two transformers succeed requires a nested case *)
(* analysis.                                    *)
(* <boxed values 236>=                          *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <stream transformers and their combinators>= *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* The common case of creating [[tx_f]] using [[pure]] *)
(* is normally written using the special operator [[< *)
(* >]], which is also pronounced ``applied to.'' *)
(* It combines a B-to-C function with an \atob  *)
(* transformer to produce an \atoc transformer. *)
(* <boxed values 237>=                          *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <stream transformers and their combinators>= *)
infix 1 <|>
fun t1 <|> t2 = (fn xs => case t1 xs of SOME y => SOME y | NONE => t2 xs) 
(* The combinator [[<*>]] creates parsers that read *)
(* things in sequence; but it can't make a choice. *)
(* If any parser in the sequence fails, the whole *)
(* sequence fails. To make a choice, as in ``[[val]] or *)
(* expression or [[define]] or [[use]],'' we use a *)
(* choice operator. The choice operator is written *)
(* [[<|>]] and pronounced ``or.'' If [[t1]] and [[t2]] *)
(* are both \atob transformers, then \monoboxt1 <|> t2 *)
(* is an \atob transformer that first tries [[t1]], then *)
(* tries [[t2]], succeeding if either succeeds, *)
(* detecting an error if either detects an error, and *)
(* failing only if both fail. To assure that the result *)
(* has a predictable type no matter which transformer is *)
(* used, both [[t1]] and [[t2]] have to have the same *)
(* type.                                        *)
(* <boxed values 239>=                          *)
val _ = op <|> : ('a, 'b) xformer * ('a, 'b) xformer -> ('a, 'b) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* I sometimes want to combine a list of parsers with *)
(* the choice operator. I can do this with a fold *)
(* operator, but I need a ``zero'' parser that always *)
(* fails.                                       *)

(* <stream transformers and their combinators>= *)
fun pzero _ = NONE
(* And except for the environment, [[test_result]] is *)
(* just like the Impcore version.               *)

(* <stream transformers and their combinators>= *)
fun anyParser ts = 
  foldr op <|> pzero ts
(* <boxed values 240>=                          *)
val _ = op pzero : ('a, 'b) xformer
(* <boxed values 240>=                          *)
val _ = op anyParser : ('a, 'b) xformer list -> ('a, 'b) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <stream transformers and their combinators>= *)
infix 6 <* *>
fun p1 <*  p2 = curry fst <$> p1 <*> p2
fun p1  *> p2 = curry snd <$> p1 <*> p2

infixr 4 <$
fun v <$ p = (fn _ => v) <$> p
(* The abbreviations are formed by modifying the [[<*>]] *)
(* or [[<>]] operator to remove the angle bracket on the *)
(* side containing the result we don't care about. For *)
(* example,                                     *)
(*                                              *)
(*   • Parser [[p1 <* p2]] reads the input of [[p1]] and *)
(*  then the input of [[p2]], but it returns only the *)
(*  result of [[p1]].                           *)
(*   • Parser [[p1 *> p2]] reads the input of [[p1]] and *)
(*  then the input of [[p2]], but it returns only the *)
(*  result of [[p2]].                           *)
(*   • Parser [[v < p]] parses the input the way [[p]] *)
(*   does, but it then ignores [[p]]'s result and *)
(*  instead produces the value [[v]].           *)
(*                                              *)
(* <boxed values 241>=                          *)
val _ = op <*  : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'b) xformer
val _ = op  *> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
val _ = op <$  : 'b               * ('a, 'c) xformer -> ('a, 'b) xformer
(* <stream transformers and their combinators>= *)
fun one xs = case streamGet xs
               of NONE => NONE
                | SOME (x, xs) => SOME (OK x, xs)
(* The simplest input-inspecting parser is [[one]]. It's *)
(* an \atoa transformer that succeeds if and only if *)
(* there is a value in the input. If there's no value *)
(* input, [[one]] fails; it never signals an error. *)
(* <boxed values 242>=                          *)
val _ = op one : ('a, 'a) xformer
(* <stream transformers and their combinators>= *)
fun eos xs = case streamGet xs
               of NONE => SOME (OK (), EOS)
                | SOME _ => NONE
(* The counterpart of [[one]] is a parser that succeeds *)
(* if and only if there is no input---that is, if we *)
(* have reached the end of a stream. This parser, which *)
(* is called [[eos]], can produce no useful result, so *)
(* it produces the empty tuple, which has type [[unit]]. *)
(* <boxed values 243>=                          *)
val _ = op eos : ('a, unit) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* Perhaps surprisingly, these are the only two standard *)
(* parsers that look at their input. The only other *)
(* parsing combinator that looks directly at input is *)
(* [[stripAndReportErrors]], which removes [[ERROR]] and *)
(* [[OK]] from error streams.                   *)

(* <stream transformers and their combinators>= *)
fun peek tx xs =
  case tx xs of SOME (OK y, _) => SOME y
              | _ => NONE
(* Function [[equalpairs]] tests for equality of atoms *)
(* and pairs. It resembles function [[equalatoms]] (\ *)
(* chunkrefscheme.chunk.equalatoms), which implements *)
(* the primitive [[=]], with two differences:   *)
(*                                              *)
(*   • Its semantics are those of [[equal?]], not [[=]]. *)
(*   • Instead of returning a micro-Scheme Boolean *)
(*  represented as a C [[Value]], it returns a  *)
(*  Boolean represented as a C [[bool]].        *)
(*                                              *)
(* [*]                                          *)
(* <boxed values 244>=                          *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <stream transformers and their combinators>= *)
fun rewind tx xs =
  case tx xs of SOME (ey, _) => SOME (ey, xs)
              | NONE => NONE
(* Given a transformer [[tx]], transformer \monobox *)
(* rewind tx computes the same value as [[tx]], but when *)
(* it's done, it rewinds the input stream back to where *)
(* it was before we ran [[tx]]. The actions performed by *)
(* [[tx]] can't be undone, but the inputs can be read *)
(* again.                                       *)
(* <boxed values 245>=                          *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <stream transformers and their combinators>= *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* Parsers based on conditions                  *)
(*                                              *)
(* Combinator [[sat]] wraps an \atob transformer with a *)
(* B-predicate such that the wrapped transformer *)
(* succeeds only when the underlying transformer *)
(* succeeds and produces a value that satisfies the *)
(* predicate.                                   *)
(* <boxed values 246>=                          *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* <stream transformers and their combinators>= *)
fun eqx y = 
  sat (fn y' => y = y') 
(* Transformer [[eqx b]] is [[sat]] specialized to an *)
(* equality predicate. It is typically used to recognize *)
(* special characters like keywords and minus signs. *)
(* <boxed values 247>=                          *)
val _ = op eqx : ''b -> ('a, ''b) xformer -> ('a, ''b) xformer
(* <stream transformers and their combinators>= *)
infixr 4 <$>?
fun f <$>? tx =
  fn xs => case tx xs
             of NONE => NONE
              | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
              | SOME (OK y, xs) =>
                  case f y
                    of NONE => NONE
                     | SOME z => SOME (OK z, xs)
(* A more subtle condition is that a partial function *)
(* can turn an input into something we're looking for. *)
(* If we have an \atob transformer, and we compose it *)
(* with a function that given a B, sometimes produces a  *)
(* C, then we get an \atoxC transformer. Because there's *)
(* a close analogy with the application operator [[<>]], *)
(* I notate this partial application operator as [[< *)
(* >?]], with a question mark.                  *)
(* <boxed values 248>=                          *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* <stream transformers and their combinators>= *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* We can run a parser conditional on the success of *)
(* another parser. Parser [[t1 < --- > t2]] succeeds *)
(* only if both [[t1]] and [[t2]] succeed at the same *)
(* point. This parser looks at enough input to decide if *)
(* [[t1]] succeeds, but it does not consume that *)
(* input---it consumes only the input of [[t2]]. *)
(* <boxed values 249>=                          *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <stream transformers and their combinators>= *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* We can also use the success or failure of a parser as *)
(* a condition. Parser \monoboxnotFollowedBy t succeeds *)
(* if and only if [[t]] fails. Parser \monobox  *)
(* notFollowedBy t may look at the input, but it never *)
(* consumes any input. I use [[notFollowedBy]] when *)
(* reading integer literals, to make sure that the *)
(* digits are not followed by a letter or other *)
(* non-delimiting symbol.                       *)
(* <boxed values 250>=                          *)
val _ = op notFollowedBy : ('a, 'b) xformer -> ('a, unit) xformer
(* <stream transformers and their combinators>= *)
fun many t = 
  curry (op ::) <$> t <*> (fn xs => many t xs) <|> pure []
(* Parsers for sequences                        *)
(*                                              *)
(* Inputs are full of sequences. A function takes a *)
(* sequence of arguments, a program is a sequence of *)
(* definitions, and a method definition contains a *)
(* sequence of expressions. To create transformers that *)
(* process sequences, I define functions [[many]] and *)
(* [[many1]]. If [[t]] is an \atob transformer, then \ *)
(* monoboxmany t is an \atoxlist-of-B transformer. *)
(* It runs [[t]] as many times as possible. And even if *)
(* [[t]] fails, \monoboxmany t always succeeds: when *)
(* [[t]] fails, \monoboxmany t returns an empty list of  *)
(* B's.                                         *)
(* <boxed values 251>=                          *)
val _ = op many  : ('a, 'b) xformer -> ('a, 'b list) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* I'd really like to write that first alternative as *)
(*                                              *)
(*  [[curry (op ::) <> t <*> many t]]           *)
(*                                              *)
(* but that formulation leads to instant death by *)
(* infinite recursion. If you write your own parsers, *)
(* it's a problem to watch out for.             *)

(* <stream transformers and their combinators>= *)
fun many1 t = 
  curry (op ::) <$> t <*> many t
(* Sometimes an empty list isn't acceptable. In that *)
(* case, use \monoboxmany1 t, which succeeds only if *)
(* [[t]] succeeds at least once---in which case it *)
(* returns a nonempty list.                     *)
(* <boxed values 252>=                          *)
val _ = op many1 : ('a, 'b) xformer -> ('a, 'b list) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* Although \monoboxmany t always succeeds, \monobox *)
(* many1 t can fail.                            *)

(* <stream transformers and their combinators>= *)
fun optional t = 
  SOME <$> t <|> pure NONE
(* Sometimes instead of zero, one, or many B's, we just *)
(* one zero or one; such a B might be called    *)
(* ``optional.'' For example, a numeric literal begins *)
(* with an optional minus sign. Function [[optional]] *)
(* turns an \atob transformer into an \atoxoptional-B *)
(* transformer. Like \monoboxmany t, \monoboxoptional t *)
(* always succeeds.                             *)
(* <boxed values 253>=                          *)
val _ = op optional : ('a, 'b) xformer -> ('a, 'b option) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <stream transformers and their combinators>= *)
infix 2 <*>!
fun tx_ef <*>! tx_x =
  fn xs => case (tx_ef <*> tx_x) xs
             of NONE => NONE
              | SOME (OK (OK y),      xs) => SOME (OK y,      xs)
              | SOME (OK (ERROR msg), xs) => SOME (ERROR msg, xs)
              | SOME (ERROR msg,      xs) => SOME (ERROR msg, xs)
infixr 4 <$>!
fun ef <$>! tx_x = pure ef <*>! tx_x
(* Error-detecting transformers and their composition *)
(*                                              *)
(* Sometimes an error is detected not by a parser but by *)
(* a function that is applied to the results of parsing. *)
(* A classic example is a function definition: if the *)
(* formal parameters are syntactically correct but *)
(* contain duplicate name, an error should be signalled. *)
(* We would transform the input into a value of type *)
(* [[name list error]]. But the transformer type already *)
(* includes the possibility of error, and we would *)
(* prefer that errors detected by functions be on the *)
(* same footing as errors detected by parsers, and that *)
(* they be handled by the same mechanisms. To enable *)
(* such handling, I define [[<*>!]] and [[<>!]] *)
(* combinators that merge function-detected errors with *)
(* parser-detected errors.                      *)
(* <boxed values 254>=                          *)
val _ = op <*>! : ('a, 'b -> 'c error) xformer * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
val _ = op <$>! : ('b -> 'c error)             * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
(* <support for source-code locations and located streams>= *)
type srcloc = string * int
fun srclocString (source, line) =
  source ^ ", line " ^ intString line
(* Source-code locations are useful when reading code *)
(* from a file. When reading code interactively, *)
(* however, a message that says the error occurred ``in *)
(* standard input, line 12,'' is more annoying than *)
(* helpful. As in the C code in \crefpage       *)
(* cinterps.error-format, I use an error format to *)
(* control when error messages include source-code *)
(* locations. The format is initially set to include *)
(* them. [*]                                    *)
(* <support for source-code locations and located streams>= *)
datatype error_format = WITH_LOCATIONS | WITHOUT_LOCATIONS
val toplevel_error_format = ref WITH_LOCATIONS
(* The format is consulted by function [[synerrormsg]], *)
(* which produces the message that accompanies a syntax *)
(* error.                                       *)
(* <support for source-code locations and located streams>= *)
fun synerrormsg (source, line) strings =
  if !toplevel_error_format = WITHOUT_LOCATIONS andalso source =
                                                                "standard input"
  then
    concat ("syntax error: " :: strings)
  else    
    concat ("syntax error in " :: srclocString (source, line) :: ": " :: strings
                                                                               )

(* Parsing bindings used in LETX forms          *)
(*                                              *)
(* A sequence of let bindings has both names and *)
(* expressions. To capture both, [[parseletbindings]] *)
(* returns a component with both [[names]] and [[exps]] *)
(* fields set.                                  *)
(* <support for source-code locations and located streams>= *)
exception Located of srcloc * exn
(* <support for source-code locations and located streams>= *)
type 'a located = srcloc * 'a
(* Tracking and reporting source-code locations *)
(*                                              *)
(* An error message is more informative if it says where *)
(* the error occurred. ``Where'' means a source-code *)
(* location. Compilers that take themselves seriously *)
(* report source-code locations right down to the *)
(* individual character: file broken.c, line 12, *)
(* column 17. In production compilers, such precision is *)
(* admirable. But in a pedagogical interpreter, the *)
(* desire for precision has to be balanced against the *)
(* need for simplicity. The best compromise is to track *)
(* only source file and line number. That's good enough *)
(* to help programmers find errors, and it eliminates *)
(* bookkeeping that would otherwise be needed to track *)
(* column numbers.                              *)
(* <boxed values 229>=                          *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* To keep track of the source location of a line, *)
(* token, expression, or other datum, I put the location *)
(* and the datum together in a pair. To make it easier *)
(* to read the types, I define a type abbreviation which *)
(* says that a value paired with a location is  *)
(* ``located.''                                 *)
(* <boxed values 229>=                          *)
type 'a located = 'a located
(* <support for source-code locations and located streams>= *)
fun atLoc loc f a =
  f a handle e as RuntimeError _ => raise Located (loc, e)
           | e as NotFound _     => raise Located (loc, e)
           (* Here are handlers for more exceptions we recognize. *)
           (* These handlers can be augmented by other,    *)
           (* language-specific handlers.                  *)
           (* <more handlers for [[atLoc]]>=               *)
           | e as IO.Io _   => raise Located (loc, e)
           | e as Div       => raise Located (loc, e)
           | e as Overflow  => raise Located (loc, e)
           | e as Subscript => raise Located (loc, e)
           | e as Size      => raise Located (loc, e)
           (* <more handlers for [[atLoc]] ((type-checking))>= *)
           | e as TypeError _         => raise Located (loc, e)
           | e as BugInTypeChecking _ => raise Located (loc, e)
(* To raise the [[Located]] exception, we use function *)
(* [[atLoc]]. Calling \monoboxatLoc f x applies [[f]] *)
(* to [[x]] within the scope of handlers that convert *)
(* recognized exceptions to the [[Located]] exception: *)
(* <boxed values 230>=                          *)
val _ = op atLoc : srcloc -> ('a -> 'b) -> ('a -> 'b)
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <support for source-code locations and located streams>= *)
fun located f (loc, a) = atLoc loc f a
fun leftLocated f ((loc, a), b) = atLoc loc f (a, b)
(* And we can call [[atLoc]] easily by using the *)
(* higher-order function [[located]]:           *)
(* <boxed values 231>=                          *)
val _ = op located : ('a -> 'b) -> ('a located -> 'b)
val _ = op leftLocated : ('a * 'b -> 'c) -> ('a located * 'b -> 'c)
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <support for source-code locations and located streams>= *)
fun fillComplaintTemplate (s, maybeLoc) =
  let val string_to_fill = " <at loc>"
      val (prefix, atloc) = Substring.position string_to_fill (Substring.full s)
      val suffix = Substring.triml (size string_to_fill) atloc
      val splice_in =
        Substring.full (case maybeLoc
                          of NONE => ""
                           | SOME (loc as (file, line)) =>
                               if      !toplevel_error_format =
                                                               WITHOUT_LOCATIONS
                               andalso file = "standard input"
                               then
                                 ""
                               else
                                 " in " ^ srclocString loc)
  in  if Substring.size atloc = 0 then (* <at loc> is not present *)
        s
      else
        Substring.concat [prefix, splice_in, suffix]
  end
fun fillAtLoc (s, loc) = fillComplaintTemplate (s, SOME loc)
fun stripAtLoc s = fillComplaintTemplate (s, NONE)
(* Once we have a location, we use it to fill in a *)
(* template for an error message. The location replaces *)
(* the string [["<at loc>"]]. The necessary string *)
(* processing is done by [[fillComplaintTemplate]], *)
(* which relies on Standard ML's [[Substring]] module. *)
(* <boxed values 232>=                          *)
val _ = op fillComplaintTemplate : string * srcloc option -> string
(* <support for source-code locations and located streams>= *)
fun errorAt msg loc = 
  ERROR (synerrormsg loc [msg])
(* <support for source-code locations and located streams>= *)
fun locatedStream (streamname, inputs) =
  let val locations = streamZip (streamRepeat streamname, streamDrop (1,
                                                                      naturals))
  in  streamZip (locations, inputs)
  end
(* To signal an error at a given location, code calls *)
(* [[errorAt]]. [*]                             *)
(* <boxed values 233>=                          *)
val _ = op errorAt : string -> srcloc -> 'a error
(* All locations originate in a located stream of lines. *)
(* The locations share a filename, and the line numbers *)
(* are 1, 2, 3, ... and so on. [*]              *)
(* <boxed values 233>=                          *)
val _ = op locatedStream : string * line stream -> line located stream
(* <streams that track line boundaries>=        *)
datatype 'a eol_marked
  = EOL of int (* number of the line that ends here *)
  | INLINE of 'a

fun drainLine EOS = EOS
  | drainLine (SUSPENDED s)     = drainLine (demand s)
  | drainLine (EOL _    ::: xs) = xs
  | drainLine (INLINE _ ::: xs) = drainLine xs
(* <streams that track line boundaries>=        *)
local 
  fun asEol (EOL n) = SOME n
    | asEol (INLINE _) = NONE
  fun asInline (INLINE x) = SOME x
    | asInline (EOL _)    = NONE
in
  fun eol    xs = (asEol    <$>? one) xs
  fun inline xs = (asInline <$>? many eol *> one) xs
  fun srcloc xs = rewind (fst <$> inline) xs
end
(* Flushing bad tokens                          *)
(*                                              *)
(* A standard parser for a batch compiler needs only to *)
(* see a stream of tokens and to know from what *)
(* source-code location each token came. A batch *)
(* compiler can simply read all its input and report all *)
(* the errors it wants to report. [Batch compilers vary *)
(* widely in the ambitions of their parsers. Some simple *)
(* parsers report just one error and stop. Some *)
(* sophisticated parsers analyze the entire input and *)
(* report the smallest number of changes needed to make *)
(* the input syntactically correct. And some    *)
(* ill-mannered parsers become confused after an error *)
(* and start spraying meaningless error messages. But *)
(* all of them have access to the entire input. *)
(* We~don't. ] But an interactive interpreter may not *)
(* use an error as an excuse to read an indefinite *)
(* amount of input. It must instead bring its error *)
(* processing to a prompt conclusion and ready itself to *)
(* read the next line. To do so, it needs to know where *)
(* the line boundaries are! For example, if I find an *)
(* error on line 6, I want to read all the tokens on *)
(* line 6, throw them away, and start over again on *)
(* line 7. The nasty bit is that I want to do it without *)
(* reading line 7---reading line 7 will take an action *)
(* and will likely have the side effect of printing a *)
(* prompt. And I want it to be the correct prompt. *)
(* I therefore define a new type constructor    *)
(* [[eol_marked]]. A value of type \monobox'a   *)
(* [[eol_marked]] is either an end-of-line marker, or it *)
(* contains a value of type [['a]] that occurs in a *)
(* line. A stream of such values can be drained up to *)
(* the end of the line. [At~some future point I~may need *)
(* to change [[drainLine]] to keep the [[EOL]] in order *)
(* to track locations in \uprolog. ]            *)
(* <boxed values 262>=                          *)
type 'a eol_marked = 'a eol_marked
val _ = op drainLine : 'a eol_marked stream -> 'a eol_marked stream
(* <boxed values 262>=                          *)
val _ = op eol      : ('a eol_marked, int) xformer
val _ = op inline   : ('a eol_marked, 'a)  xformer
val _ = op srcloc   : ('a located eol_marked, srcloc) xformer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <support for lexical analysis>=              *)
type 'a lexer = (char, 'a) xformer
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(* \catcode`=\other \catcode`_=\other \catcode`$=\other *)
(*                                              *)
(*  \toprule Lexical analyzers; tokens          *)
(*  \midrule \type'a lexer = (char, 'a) xformer \ *)
(*  tableboxisDelim : char -> bool \tablebox    *)
(*  whitespace : char list lexer \tableboxintChars : *)
(*  (char -> bool) -> char list lexer \tablebox *)
(*  intFromChars : char list -> int error \tablebox *)
(*  intToken : (char -> bool) -> int lexer \typetoken *)
(*  \tableboxisLiteral : string -> token -> bool \ *)
(*  tableboxtokenString : token -> string \tablebox *)
(*  lexLineWith : token lexer -> line -> token stream *)
(*  [8pt] \midrule Streams with end-of-line markers *)
(*  \type'a eol_marked \tableboxdrainLine : 'a  *)
(*  eol_marked stream -> 'a eol_marked stream [8pt] \ *)
(*  midrule Parsers                             *)
(*  \type'a parser = (token located eol_marked, 'a) *)
(*  xformer \tableboxeol : ('a eol_marked, int) *)
(*  xformer \tableboxinline : ('a eol_marked, 'a) *)
(*  xformer \tableboxtoken : token parser \tablebox *)
(*  srcloc : srcloc parser \tableboxnoTokens : unit *)
(*  parser \tablebox@@ : 'a parser -> 'a located *)
(*  parser \tablebox<?> : 'a parser * string -> 'a *)
(*  parser \tablebox<!> : 'a parser * string -> 'b *)
(*  parser \tableboxliteral : string -> unit parser \ *)
(*  tablebox>-- : string * 'a parser -> 'a parser \ *)
(*  tablebox--< : 'a parser * string -> 'a parser \ *)
(*  tableboxbracket : string * string * 'a parser -> *)
(*  'a parser \splitboxnodupsstring * string -> *)
(*  srcloc * name list-> name list error \tablebox *)
(*  safeTokens : token located eol_marked stream -> *)
(*  token list \tableboxechoTagStream : line stream *)
(*  -> line stream \tableboxstripAndReportErrors : 'a *)
(*  error stream -> 'a stream [8pt] \midrule A  *)
(*  complete, interactive source of abstract syntax *)
(*  \splitboxinteractiveParsedStreamtoken lexer * 'a *)
(*  parser -> string * line stream * prompts -> 'a *)
(*  stream \bottomrule                          *)
(*                                              *)
(* Transformers specialized for lexical analysis or *)
(* parsing [*]                                  *)
(*                                              *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(*                                              *)
(* Lexical analyzers: transformers of characters *)
(*                                              *)
(* The interpreters in this book consume one line at a *)
(* time. But characters within a line may be split into *)
(* multiple tokens. For example, the line       *)
(*                                              *)
(*   (define list1 (x) (cons x '()))            *)
(*                                              *)
(* should be split into the tokens              *)
(*                                              *)
(*                                              *)
(*  (                                           *)
(*  define                                      *)
(*  list1                                       *)
(*  (                                           *)
(*  x                                           *)
(*  )                                           *)
(*  (                                           *)
(*  cons                                        *)
(*  x                                           *)
(*  '                                           *)
(*  (                                           *)
(*  )                                           *)
(*  )                                           *)
(*  )                                           *)
(*                                              *)
(* This section defines reusable transformers that are *)
(* specialized to transform streams of characters into *)
(* something else, usually tokens.              *)
(* <boxed values 255>=                          *)
type 'a lexer = 'a lexer
(* The type [['a lexer]] should be pronounced ``lexer *)
(* returning [['a]].''                          *)

(* <support for lexical analysis>=              *)
fun isDelim c =
  Char.isSpace c orelse Char.contains "()[]{};" c
(* In popular languages, a character like a semicolon or *)
(* comma usually does not join with other tokens to form *)
(* a character. In this book, left and right brackets of *)
(* all shapes keep to themselves and don't group with *)
(* other characters. And in just about every    *)
(* non-esoteric language, blank space separates tokens. *)
(* A character whose presence marks the end of one token *)
(* (and possibly the beginning of the next) is called a *)
(* delimiter. In this book, the main delimiter  *)
(* characters are whitespace and parentheses. The other *)
(* delimiter is the semicolon, which introduces a *)
(* comment. [*]                                 *)
(* <boxed values 256>=                          *)
val _ = op isDelim : char -> bool
(* [[Char.isSpace]] recognizes all whitespace   *)
(* characters. [[Char.contains]] takes a string and a *)
(* character and says if the string contains the *)
(* character. These functions are in the initial basis *)
(* of Standard ML.                              *)

(* <support for lexical analysis>=              *)
val whitespace = many (sat Char.isSpace one)
(* All languages in this book ignore whitespace. Lexer *)
(* [[whitespace]] is typically combined with another *)
(* lexer using the [[*>]] operator.             *)
(* <boxed values 257>=                          *)
val _ = op whitespace : char list lexer
(* <support for lexical analysis>=              *)
fun intChars isDelim = 
  (curry (op ::) <$> eqx #"-" one <|> pure id) <*> many1 (sat Char.isDigit one)
                                                                              <*
  notFollowedBy (sat (not o isDelim) one)
(* The rules for integer literals are as follows: *)
(*                                              *)
(*   • The integer literal may begin with a minus sign. *)
(*   • It continues with one or more digits.  *)
(*   • If it is followed by character, that character *)
(*  must be a delimiter. (In other words, it must not *)
(*  be followed by a non-delimiter.)            *)
(*   • When the sequence of digits is converted to an *)
(*  [[int]], the arithmetic used in the conversion *)
(*  must not overflow.                          *)
(*                                              *)
(* Function [[intChars]] does the lexical analysis to *)
(* grab the characters; [[intFromChars]] handles the *)
(* conversion and its potential overflow, and   *)
(* [[intToken]] puts everything together. Because not *)
(* every language uses the same delimiters, both *)
(* [[intChars]] and [[intToken]] receive a predicate *)
(* that identifies delimiters.                  *)
(* <boxed values 258>=                          *)
val _ = op intChars : (char -> bool) -> char list lexer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* Function [[Char.isDigit]], like [[Char.isSpace]], is *)
(* part of Standard ML.                         *)

(* <support for lexical analysis>=              *)
fun intFromChars (#"-" :: cs) = 
      intFromChars cs >>=+ Int.~
  | intFromChars cs =
      (OK o valOf o Int.fromString o implode) cs
      handle Overflow => ERROR
                        "this interpreter can't read arbitrarily large integers"
(* Function [[intFromChars]] composes three functions *)
(* from Standard ML's initial basis. Function   *)
(* [[implode]] converts a list of characters to a *)
(* string; [[Int.fromString]] converts a string to an \ *)
(* monoboxint option (raising [[Overflow]] if the *)
(* literal is too big); and [[valOf]] converts an \ *)
(* monoboxint option to an [[int]]. The [[Int. ]] *)
(* function, which is used when we see a minus sign, *)
(* negates an integer. The [[ ]] is meant to resemble a *)
(* ``high minus'' sign, a notational convention that *)
(* goes back at least to \apl.                  *)
(* <boxed values 259>=                          *)
val _ = op intFromChars : char list -> int error
(* <support for lexical analysis>=              *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* In this book, every language except uProlog can use *)
(* [[intToken]].                                *)
(* <boxed values 260>=                          *)
val _ = op intToken : (char -> bool) -> int lexer
(* <support for lexical analysis>=              *)
datatype bracket_shape = ROUND | SQUARE | CURLY

fun leftString ROUND  = "("
  | leftString SQUARE = "["
  | leftString CURLY  = "{"
fun rightString ROUND  = ")"
  | rightString SQUARE = "]"
  | rightString CURLY = "}"
(* <support for lexical analysis>=              *)
datatype 'a plus_brackets
  = LEFT  of bracket_shape
  | RIGHT of bracket_shape
  | PRETOKEN of 'a

fun bracketLexer pretoken
  =  LEFT  ROUND  <$ eqx #"(" one
 <|> LEFT  SQUARE <$ eqx #"[" one
 <|> LEFT  CURLY  <$ eqx #"{" one
 <|> RIGHT ROUND  <$ eqx #")" one
 <|> RIGHT SQUARE <$ eqx #"]" one
 <|> RIGHT CURLY  <$ eqx #"}" one
 <|> PRETOKEN <$> pretoken

fun plusBracketsString _   (LEFT shape)  = leftString shape
  | plusBracketsString _   (RIGHT shape) = rightString shape
  | plusBracketsString pts (PRETOKEN pt)  = pts pt
(* Given a lexer for language tokens, we can build a *)
(* lexer for tokens:                            *)
(* <boxed values 261>=                          *)
type 'a plus_brackets = 'a plus_brackets
val _ = op bracketLexer : 'a lexer -> 'a plus_brackets lexer
(* The code is divided among these chunks:      *)
(* <common parsing code>=                       *)
(* A value of type [['a parser]] takes a stream of *)
(* located tokens set between end-of-line markers, and *)
(* it returns a value of type [['a]], plus any leftover *)
(* tokens.                                      *)
(* <combinators and utilities for parsing located streams>= *)
type ('t, 'a) polyparser = ('t located eol_marked, 'a) xformer
(* <combinators and utilities for parsing located streams>= *)
fun token    stream = (snd <$> inline)      stream
fun noTokens stream = (notFollowedBy token) stream
(* The [[EOL]] and [[INLINE]] constructors are essential *)
(* for error recovery, but for parsing, they just get in *)
(* the way. Our first order of business is to define *)
(* analogs of [[one]] and [[eos]] that ignore [[EOL]]. *)
(* Parser [[token]] takes one token; parser [[srcloc]] *)
(* looks at the source-code location of a token, but *)
(* leaves the token in the input; and parser    *)
(* [[noTokens]] succeeds only if there are no tokens *)
(* left in the input. They are built on top of  *)
(* ``utility'' parsers [[eol]] and [[inline]]. The two *)
(* utility parsers have different contracts; [[eol]] *)
(* succeeds only when at [[EOL]], but [[inline]] scans *)
(* past [[EOL]] to look for [[INLINE]].         *)
(* <boxed values 263>=                          *)
val _ = op token    : ('t, 't)   polyparser
val _ = op noTokens : ('t, unit) polyparser
(* <combinators and utilities for parsing located streams>= *)
fun @@ p = pair <$> srcloc <*> p
(* Sometimes the easiest way to keep track of   *)
(* source-code locations is to pair a source-code *)
(* location with a result from a parser. This happens *)
(* just often enough that I find it worth while to *)
(* define the [[@@]] function. (Associate the word *)
(* ``at'' with the idea of ``location.'') The code uses *)
(* a dirty trick: it works because [[srcloc]] looks at *)
(* the input but does not consume any tokens.   *)
(* <boxed values 264>=                          *)
val _ = op @@ : ('t, 'a) polyparser -> ('t, 'a located) polyparser
(* <combinators and utilities for parsing located streams>= *)
infix 0 <?>
fun p <?> what = p <|> errorAt ("expected " ^ what) <$>! srcloc
(* Parsers that report errors                   *)
(*                                              *)
(* Most syntactic forms (expressions, unit tests, *)
(* definitions, and so on) are parsed by trying a set of *)
(* alternatives. When all alternatives fail, I usually *)
(* want to convert the failure into an error. Parser \ *)
(* monoboxp <?> what succeeds when [[p]] succeeds, but *)
(* when [[p]] fails, parser \monoboxp <?> what reports *)
(* an error: it expected [[what]]. The error says what *)
(* the parser was expecting, and it gives the   *)
(* source-code location of the unrecognized token. *)
(* If there is no token, there is no error---at end of *)
(* file, rather than signal an error, a parser made *)
(* using [[<?>]] fails. You can see an example in the *)
(* parser for extended definitions in \chunkref *)
(* mlschemea.chunk.xdef. [*]                    *)
(* <boxed values 265>=                          *)
val _ = op <?> : ('t, 'a) polyparser * string -> ('t, 'a) polyparser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* The [[<?>]] operator must not be used to define a *)
(* parser that is passed to [[many]], [[many1]], or *)
(* [[optional]] In that context, if parser [[p]] fails, *)
(* it must not signal an error; it must instead *)
(* propagate the failure to [[many]], [[many1]], or *)
(* [[optional]], so those combinators know there is not *)
(* a [[p]] there.                               *)

(* <combinators and utilities for parsing located streams>= *)
infix 4 <!>
fun p <!> msg =
  fn tokens => (case p tokens
                  of SOME (OK _, unread) =>
                       (case peek srcloc tokens
                          of SOME loc => SOME (errorAt msg loc, unread)
                           | NONE => NONE)
                   | _ => NONE)
(* Another common error-detecting technique is to use a *)
(* parser [[p]] to detect some input that shouldn't be *)
(* there. For example, if we're just starting to read a *)
(* definition, the input shouldn't begin with a right *)
(* parenthesis. I can write a parser [[p]] that *)
(* recognizes a right parenthesis, but I can't simply *)
(* combine [[p]] with [[errorAt]] and [[srcloc]] in the *)
(* same way that [[<?>]] does, because I have two goals: *)
(* consume the tokens recognized by [[p]], and also *)
(* report the error at the location of the first of *)
(* those tokens. I can't use [[errorAt]] until after *)
(* [[p]] succeeds, but I have to use [[srcloc]] on the *)
(* input stream as it is before [[p]] is run. I solve *)
(* this problem by defining a special combinator that *)
(* keeps a copy of the tokens inspected by [[p]]. *)
(* If parser [[p]] succeeds, then parser [[p <!> msg]] *)
(* consumes the tokens consumed by [[p]] and reports *)
(* error [[msg]] at the location of [[p]]'s first token. *)
(* <boxed values 266>=                          *)
val _ = op <!> : ('t, 'a) polyparser * string -> ('t, 'b) polyparser
(* <combinators and utilities for parsing located streams>= *)
fun nodups (what, context) (loc, names) =
  let fun dup [] = OK names
        | dup (x::xs) = if List.exists (fn y : string => y = x) xs then
                          errorAt (what ^ " " ^ x ^ " appears twice in " ^
                                                                    context) loc
                        else
                          dup xs
  in  dup names
  end
(* Detection of duplicate names                 *)
(*                                              *)
(* Most of the languages in this book allow you to *)
(* define functions or methods that take formal *)
(* parameters. It is never permissible to use the same *)
(* name for formal parameters in two different  *)
(* positions. There are surprisingly many other places *)
(* where it's not acceptable to have duplicates in a *)
(* list of strings. Function [[nodups]] takes two *)
(* Curried arguments: a pair saying what kind of thing *)
(* might be duplicated and where it appeared, followed *)
(* by a pair containing a list of names and the *)
(* source-code location of the list. If there are no *)
(* duplicates, it returns [[OK]] applied to the list of *)
(* names; otherwise it returns an [[ERROR]].    *)
(* <boxed values 270>=                          *)
val _ = op nodups : string * string -> srcloc * name list -> name list error
(* Function [[List.exists]] is like the micro-Scheme *)
(* [[exists?]]. It is in the initial basis for  *)
(* Standard ML.                                 *)

(* Once the parser sees the opening parenthesis and the *)
(* keyword, failure is impossible: either parser [[p]] *)
(* parses stuff correctly, or there's an error. [*] *)
(* <transformers for interchangeable brackets>= *)
fun notCurly (_, CURLY) = false
  | notCurly _          = true

(* left: takes shape, succeeds or fails
   right: takes shape and
      succeeds with right bracket of correct shape
      errors with right bracket of incorrect shape
      fails with token that is not right bracket *)

fun left  tokens = ((fn (loc, LEFT  s) => SOME (loc, s) | _ => NONE) <$>? inline
                                                                        ) tokens
fun right tokens = ((fn (loc, RIGHT s) => SOME (loc, s) | _ => NONE) <$>? inline
                                                                        ) tokens
fun leftCurly tokens = sat (not o notCurly) left tokens

fun atRight expected = rewind right <?> expected

fun badRight msg =
  (fn (loc, shape) => errorAt (msg ^ " " ^ rightString shape) loc) <$>! right
(* Parser [[right]] matches a right bracket by itself. *)
(* But quite commonly, we want to wrap another parser  *)
(* [[p]] in matching left and right brackets.   *)
(* If something goes wrong---say the brackets don't *)
(* match---we ought not to try to address the error in *)
(* the right-bracket parser alone; we need to be able to *)
(* report the location of the left bracket as well. *)
(* To be able to issue good error messages, I define *)
(* parser [[matchingRight]], which always succeeds and *)
(* which produces one of three outcomes:        *)
(*                                              *)
(*   • Result \monobox[[FOUND_RIGHT]] (loc, s) says we *)
(*  found a right bracket exactly where we expected *)
(*  to, and its shape and location are s and loc. *)

(* <transformers for interchangeable brackets>= *)
type ('t, 'a) pb_parser = ('t plus_brackets, 'a) polyparser
datatype right_result
  = FOUND_RIGHT      of bracket_shape located
  | SCANNED_TO_RIGHT of srcloc  (* location where scanning started *)
  | NO_RIGHT

fun scanToClose tokens = 
  let val loc = getOpt (peek srcloc tokens, ("end of stream", 9999))
      fun scan lpcount tokens =
        (* lpcount is the number of unmatched left parentheses *)
        case tokens
          of EOL _                  ::: tokens => scan lpcount tokens
           | INLINE (_, LEFT  t)    ::: tokens => scan (lpcount+1) tokens
           | INLINE (_, RIGHT t)    ::: tokens => if lpcount = 0 then
                                                    pure (SCANNED_TO_RIGHT loc)
                                                                          tokens
                                                  else
                                                    scan (lpcount-1) tokens
           | INLINE (_, PRETOKEN _) ::: tokens => scan lpcount tokens
           | EOS         => pure NO_RIGHT tokens
           | SUSPENDED s => scan lpcount (demand s)
  in  scan 0 tokens
  end

fun matchingRight tokens = (FOUND_RIGHT <$> right <|> scanToClose) tokens

fun matchBrackets _ (loc, left) _ NO_RIGHT =
      errorAt ("unmatched " ^ leftString left) loc
  | matchBrackets e (loc, left) _ (SCANNED_TO_RIGHT loc') =
      errorAt ("expected " ^ e) loc
  | matchBrackets _ (loc, left) a (FOUND_RIGHT (loc', right)) =
      if left = right then
        OK a
      else
        errorAt (rightString right ^ " does not match " ^ leftString left ^
                 (if loc <> loc' then " at " ^ srclocString loc else "")) loc'
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(* Function [[matchBrackets]] takes this result, along *)
(* with the left bracket and the parsed result a, and *)
(* knows what to do.                            *)
(* <boxed values 267>=                          *)
type right_result = right_result
val _ = op matchingRight : ('t, right_result) pb_parser
val _ = op scanToClose   : ('t, right_result) pb_parser
val _ = op matchBrackets : string -> bracket_shape located -> 'a -> right_result
                                                                     -> 'a error
(* <transformers for interchangeable brackets>= *)
fun liberalBracket (expected, p) =
  matchBrackets expected <$> sat notCurly left <*> p <*>! matchingRight
fun bracketKeyword (keyword, expected, p) =
  liberalBracket (expected, keyword *> (p <?> expected))
fun bracket (expected, p) =
  liberalBracket (expected, p <?> expected)
fun curlyBracket (expected, p) =
  matchBrackets expected <$> leftCurly <*> (p <?> expected) <*>! matchingRight
(* Story:                                       *)
(*                                              *)
(*   • Parser can fail, right bracket has to match: *)
(*  [[liberalBracket]]                          *)
(*   • Keyword can fail, but if it matches, parser has *)
(*  to match: [[bracketKeyword]]                *)
(*   • Left bracket can fail, but if it matches, parser *)
(*  has to match: [[bracket]], [[curlyBracket]] *)
(*                                              *)
(* <boxed values 268>=                          *)
val _ = op bracketKeyword : ('t, 'keyword) pb_parser * string * ('t, 'a)
                                                 pb_parser -> ('t, 'a) pb_parser
(* <transformers for interchangeable brackets>= *)
fun usageParser keyword =
  let val left = eqx #"(" one <|> eqx #"[" one
      val getkeyword = left *> (implode <$> many1 (sat (not o isDelim) one))
  in  fn (usage, p) =>
        case getkeyword (streamOfList (explode usage))
          of SOME (OK k, _) => bracketKeyword (keyword k, usage, p)
           | _ => let exception BadUsage of string in raise BadUsage usage end
  end
(* Usually, we want to pull the keyword out of the usage *)
(* string. [*]                                  *)
(* <boxed values 269>=                          *)
val _ = op usageParser : (string -> ('t, string) pb_parser) -> string * ('t, 'a)
                                                 pb_parser -> ('t, 'a) pb_parser
(* Hello, stranger?                             *)
(* <transformers for interchangeable brackets>= *)
fun pretoken stream = ((fn PRETOKEN t => SOME t | _ => NONE) <$>? token) stream
(* <code used to debug parsers>=                *)
fun safeTokens stream =
  let fun tokens (seenEol, seenSuspended) =
            let fun get (EOL _         ::: ts) = if seenSuspended then []
                                                 else tokens (true, false) ts
                  | get (INLINE (_, t) ::: ts) = t :: get ts
                  | get  EOS                   = []
                  | get (SUSPENDED (ref (PRODUCED ts))) = get ts
                  | get (SUSPENDED s) = if seenEol then []
                                        else tokens (false, true) (demand s)
            in   get
            end
  in  tokens (false, false) stream
  end
(* Code used to debug parsers                   *)
(*                                              *)
(* When debugging parsers, I often find it helpful to *)
(* dump out the tokens that a parser is looking at. *)
(* I want to dump all the tokens that are available *)
(* without triggering the action of reading another line *)
(* of input. I believe it's safe to read until I have *)
(* got to both an end-of-line marker and a suspension *)
(* whose value has not yet been demanded.       *)
(* <boxed values 271>=                          *)
val _ = op safeTokens : 'a located eol_marked stream -> 'a list
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <code used to debug parsers>=                *)
fun showErrorInput asString p tokens =
  case p tokens
    of result as SOME (ERROR msg, rest) =>
         if String.isSubstring " [input: " msg then
           result
         else
           SOME (ERROR (msg ^ " [input: " ^
                        spaceSep (map asString (safeTokens tokens)) ^ "]"),
               rest)
     | result => result
(* The [[showErrorInput]] function transforms an *)
(* ordinary parser into a parser that, when it errors, *)
(* shows the input that caused the error. It should be *)
(* applied routinely to every parser you build. *)
(* <boxed values 272>=                          *)
val _ = op showErrorInput : ('t -> string) -> ('t, 'a) polyparser -> ('t, 'a)
                                                                      polyparser
(* <code used to debug parsers>=                *)
fun wrapAround tokenString what p tokens =
  let fun t tok = " " ^ tokenString tok
      val _ = app eprint ["Looking for ", what, " at"]
      val _ = app (eprint o t) (safeTokens tokens)
      val _ = eprint "\n"
      val answer = p tokens
      val _ = app eprint [case answer of NONE => "Didn't find " | SOME _ =>
                                                                       "Found ",
                         what, "\n"]
  in  answer
  end handle e => ( app eprint ["Search for ", what, " raised ", exnName e, "\n"
                                                                               ]
                  ; raise e)
(* The [[wrapAround]] function can be used to wrap a *)
(* parser; it shows what the parser was looking for, *)
(* what tokens it was looking at, and whether it found *)
(* something.                                   *)
(* <boxed values 273>=                          *)
val _ = op wrapAround : ('t -> string) -> string -> ('t, 'a) polyparser -> ('t,
                                                                  'a) polyparser
(* <streams that issue two forms of prompts>=   *)
fun echoTagStream lines = 
  let fun echoIfTagged line =
        if (String.substring (line, 0, 2) = ";#" handle _ => false) then
          print line
        else
          ()
  in  postStream (lines, echoIfTagged)
  end
(* Testing support                              *)
(*                                              *)
(* Let's get the testing support out of the way first. *)
(* As in the C code, I want to print out any line read *)
(* that begins with the special string [[;#]]. This *)
(* string is a formal comment that helps me test chunks *)
(* marked \LAtranscript\RA. In the ML code, I can do the *)
(* job in a very modular way: I define a post-stream *)
(* action that prints any line meeting the criterion. *)
(* Function [[echoTagStream]] transforms a stream of *)
(* lines to a stream of lines, adding the behavior *)
(* I want.                                      *)
(* <boxed values 274>=                          *)
val _ = op echoTagStream : line stream -> line stream 
(* <streams that issue two forms of prompts>=   *)
fun stripAndReportErrors xs =
  let fun next xs =
        case streamGet xs
          of SOME (ERROR msg, xs) => (eprintln msg; next xs)
           | SOME (OK x, xs) => SOME (x, xs)
           | NONE => NONE
  in  streamOfUnfold next xs
  end
(* Issuing messages for error values            *)
(*                                              *)
(* Function [[stripAndReportErrors]] removes the *)
(* [[ERROR]] and [[OK]] tags from a stream, producing an *)
(* output stream with a simpler type. Values tagged with *)
(* [[OK]] are passed on to the output stream unchanged; *)
(* messages tagged with [[ERROR]] are printed to *)
(* standard error, using [[eprintln]].          *)
(* <boxed values 275>=                          *)
val _ = op stripAndReportErrors : 'a error stream -> 'a stream
(* <streams that issue two forms of prompts>=   *)
fun lexLineWith lexer =
  stripAndReportErrors o streamOfUnfold lexer o streamOfList o explode
(* An error detected during lexical analysis is printed *)
(* without any information about source-code locations. *)
(* That's because, to keep things somewhat simple, *)
(* I've chosen to do lexical analysis on one line at a *)
(* time, and I don't keep track of the line's   *)
(* source-code location.                        *)
(* <boxed values 276>=                          *)
val _ = op lexLineWith : 't lexer -> line -> 't stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <streams that issue two forms of prompts>=   *)
fun parseWithErrors parser =
  let fun adjust (SOME (ERROR msg, tokens)) = SOME (ERROR msg, drainLine tokens)
        | adjust other = other
  in  streamOfUnfold (adjust o parser)
  end
(* When an error occurs during parsing, I drain the rest *)
(* of the tokens on the line where the error occurred. *)
(* I don't strip the errors at this point; errors are *)
(* passed on to the interactive stream because when an *)
(* error is detected, the prompt may need to be changed. *)
(* <boxed values 277>=                          *)
val _ = op parseWithErrors : ('t, 'a) polyparser -> 't located eol_marked stream
                                                              -> 'a error stream
(* <streams that issue two forms of prompts>=   *)
type prompts   = { ps1 : string, ps2 : string }
val stdPrompts = { ps1 = "-> ", ps2 = "   " }
val noPrompts  = { ps1 = "", ps2 = "" }
(* Prompts                                      *)
(*                                              *)
(* All interpreters in the book are built on the Unix *)
(* shell model of having two prompt strings. The first *)
(* prompt string, called [[ps1]], is issued when *)
(* starting to read a definition. The second prompt *)
(* string, called [[ps2]], is issued when in the middle *)
(* of reading a definition. To turn prompting off, we *)
(* set both to the empty string.                *)
(* <boxed values 278>=                          *)
type prompts = prompts
val _ = op stdPrompts : prompts
val _ = op noPrompts  : prompts
(* <streams that issue two forms of prompts>=   *)
fun ('t, 'a) interactiveParsedStream (lexer, parser) (name, lines, prompts) =
  let val { ps1, ps2 } = prompts
      val thePrompt = ref ps1
      fun setPrompt ps = fn _ => thePrompt := ps

      val lines = preStream (fn () => print (!thePrompt), echoTagStream lines)

      fun lexAndDecorate (loc, line) =
        let val tokens = postStream (lexLineWith lexer line, setPrompt ps2)
        in  streamMap INLINE (streamZip (streamRepeat loc, tokens)) @@@
            streamOfList [EOL (snd loc)]
        end

      val xdefs_with_errors : 'a error stream = 
        (parseWithErrors parser o streamConcatMap lexAndDecorate o locatedStream
                                                                               )
        (name, lines)
(* To deliver the right prompt in the right situation, *)
(* I store the current prompt in a mutable cell called *)
(* [[thePrompt]]. The prompt is initially [[ps1]], and *)
(* it stays [[ps1]] until a token is delivered, at which *)
(* point the [[postStream]] action sets the prompt to  *)
(* [[ps2]]. But when we are about to get a new  *)
(* definition, a [[preStream]] action on the syntax *)
(* stream [[xdefs_with_errors]] resets the prompt to  *)
(* [[ps1]]. This combination of pre- and post-stream *)
(* actions, on different streams, makes sure the prompt *)
(* is always appropriate to the state of the parser. [*] *)
(* <boxed values 279>=                          *)
val _ = op interactiveParsedStream : 't lexer * ('t, 'a) polyparser -> string *
                                              line stream * prompts -> 'a stream
val _ = op lexAndDecorate : srcloc * line -> 't located eol_marked stream
  in  
      stripAndReportErrors (preStream (setPrompt ps1, xdefs_with_errors))
  end 
(* The functions defined in this appendix are useful for *)
(* reading all kinds of input, not just computer *)
(* programs, and I encourage you to use them in your own *)
(* projects. But here are two words of caution: with so *)
(* many abstractions in the mix, the parsers are tricky *)
(* to debug. And while some parsers built from  *)
(* combinators are very efficient, mine aren't. *)

(* <common parsing code ((elided))>=            *)
fun ('t, 'a) finiteStreamOfLine fail (lexer, parser) line =
  let val lines = streamOfList [line] @@@ streamOfEffects fail
      fun lexAndDecorate (loc, line) =
        let val tokens = lexLineWith lexer line
        in  streamMap INLINE (streamZip (streamRepeat loc, tokens)) @@@
            streamOfList [EOL (snd loc)]
        end

      val things_with_errors : 'a error stream = 
        (parseWithErrors parser o streamConcatMap lexAndDecorate o locatedStream
                                                                               )
        ("command line", lines)
  in  
      stripAndReportErrors things_with_errors
  end 
val _ = finiteStreamOfLine :
          (unit -> string option) -> 't lexer * ('t, 'a) polyparser -> line ->
                                                                       'a stream
(* <shared utility functions for initializing interpreters>= *)
fun override_if_testing () =                           (*OMIT*)
  if isSome (OS.Process.getEnv "NOERRORLOC") then      (*OMIT*)
    toplevel_error_format := WITHOUT_LOCATIONS         (*OMIT*)
  else                                                 (*OMIT*)
    ()                                                 (*OMIT*)
fun setup_error_format interactivity =
  if prompts interactivity then
    toplevel_error_format := WITHOUT_LOCATIONS
    before override_if_testing () (*OMIT*)
  else
    toplevel_error_format := WITH_LOCATIONS
    before override_if_testing () (*OMIT*)
(* Utility function for limiting the depth of recursion *)
(*                                              *)
(* If there's no other overhead, MLton delivers *)
(* 25 million evals per second. Finding all solutions to *)
(* a Boolean formula requires on the order of 200. *)
(* <function application with overflow checking>= *)
local
  val throttleCPU = case OS.Process.getEnv "BPCOPTIONS"
                      of SOME "nothrottle" => false
                       | _ => true
  val defaultRecursionLimit = 6000 (* about 1/5 of 32,000? *)
  val recursionLimit = ref defaultRecursionLimit
  val evalFuel       = ref 1000000
  datatype checkpoint = RECURSION_LIMIT of int
in
  val defaultEvalFuel = ref (!evalFuel)
  fun withFuel n f x = 
    let val old = !evalFuel
        val _ = evalFuel := n
    in  (f x before evalFuel := old) handle e => (evalFuel := old; raise e)
    end

  fun fuelRemaining () = !evalFuel

  fun checkpointLimit () = RECURSION_LIMIT (!recursionLimit)
  fun restoreLimit (RECURSION_LIMIT n) = recursionLimit := n

  fun applyCheckingOverflow f =
    if !recursionLimit <= 0 then
      raise RuntimeError "recursion too deep"
    else if throttleCPU andalso !evalFuel <= 0 then
      (evalFuel := !defaultEvalFuel; raise RuntimeError "CPU time exhausted")
    else
      let val _ = recursionLimit := !recursionLimit - 1
          val _ = evalFuel        := !evalFuel - 1
      in  fn arg => f arg before (recursionLimit := !recursionLimit + 1)
      end
  fun resetOverflowCheck () = ( recursionLimit := defaultRecursionLimit
                              ; evalFuel := !defaultEvalFuel
                              )
end
(* Utility function for mutual recursion        *)
(*                                              *)
(* In Standard ML, mutually recursive functions are *)
(* typically defined using the [[and]] keyword. But such *)
(* a definition requires that the functions be adjacent *)
(* in the source code. When there are large mutual *)
(* recursions in which many functions participate, it is *)
(* often simpler to implement mutual recursion the way a *)
(* C programmer does: \stdbreak put each function in a *)
(* mutable reference cell and call indirectly through *)
(* the contents of that cell. But how is the cell to be *)
(* initialized? In C, initialization is handled by the *)
(* linker. In ML, we have to initialize the reference *)
(* cell when we create it; \stdbreak the cell doesn't *)
(* get its final value until the function it refers to *)
(* is defined. To initialize such a cell, I use function *)
(* [[forward]] to create an initial function. That *)
(* initial function, if ever called, causes a fatal *)
(* error. [*]                                   *)
(* <function [[forward]], for mutual recursion through mutable reference cells>= *)
fun forward what _ =
  let exception UnresolvedForwardDeclaration of string
  in  raise UnresolvedForwardDeclaration what
  end
(* For an example of [[forward]], see \string\chunkref: *)
(* chunk.first-use-of-forward. (THIS COULD POSSIBLY BE *)
(* ELIMINATED.)                                 *)

exception LeftAsExercise of string



(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES FOR \MCL                         *)
(*                                                               *)
(*****************************************************************)

(* <abstract syntax and values for \mcl>=       *)
(* <paths for \mcl>=                            *)
type modcon = { printName : name, serial : int }
datatype modident = MODCON of modcon | MODTYPLACEHOLDER of name

(* Refugees from the chapter (type checking)    *)
(*                                              *)
(* Path and type basics                         *)
(*                                              *)
(* <definition of function [[genmodident]]>=    *)
local
  val timesDefined : int env ref = ref emptyEnv
     (* how many times each modident is defined *)
in
  fun genmodident name =
    let val n = find (name, !timesDefined) handle NotFound _ => 0
val n = 0 (* XXX fix this later *)
        val _ = timesDefined := bind (name, n + 1, !timesDefined)
    in  MODCON { printName = name, serial = n }
    end
end
(* <boxed values 129>=                          *)
val _ = op genmodident : name -> modident
(* XXX TODO: re-do stamping as in uML. Note: a path in a *)
(* module-type definition starts with           *)
(* [[MODTYPLACEHOLDER]].                        *)


datatype 'modname path' = PNAME of 'modname
                        | PDOT of 'modname path' * name
                        | PAPPLY of 'modname path' * 'modname path' list

type pathex = name located path'
type path   = modident path'
(* <paths for \mcl>=                            *)
fun plast (PDOT (_, x)) = x
  | plast (PNAME (_, x)) = x
  | plast (PAPPLY _) = "??last??"
(* <definition of [[ty]] for \mcl>=             *)
datatype 'modname ty' = TYNAME of 'modname path'
                      | FUNTY  of 'modname ty' list * 'modname ty'
                      | ANYTYPE   (* type of (error ...) *)
type tyex = name located ty'
type ty   = modident ty'
(* Declarations and module types                *)
(*                                              *)
(* Maybe [[dec_component]] should be [[decty]]? *)
(*                                              *)
(* A [[ENVMOD]] has a module identifier only if it is a *)
(* top-level module and has been elaborated. MAYBE WHAT *)
(* WE NEED INSTEAD IS FOR EVERY ENVMOD TO HAVE A PATH? *)
(* <definition of [[modty]] for \mcl>=          *)
datatype modty
  = MTEXPORTS of (name * component) list
  | MTARROW   of (modident * modty) list * modty
  | MTALLOF   of modty list
and component
  = COMPVAL    of ty
  | COMPMANTY  of ty
  | COMPABSTY  of path
  | COMPMOD    of modty

type 'a rooted = 'a * path
fun root (_, path) = path
fun rootedMap f (a, path) = (f a, path)

datatype binding
  = ENVVAL    of ty
  | ENVMANTY  of ty
  | ENVMOD    of modty rooted
  | ENVOVLN   of ty list  (* overloaded name *)
  | ENVMODTY  of modty

datatype decl
  = DECVAL    of tyex
  | DECABSTY
  | DECMANTY  of tyex
  | DECMOD    of modtyx
  | DECMODTY  of modtyx  (* only at top level *)
and modtyx
  = MTNAMEDX   of name
  | MTEXPORTSX of (name * decl) located list
  | MTALLOFX   of modtyx located list
  | MTARROWX   of (name located * modtyx located) list * modtyx located
type vcon = name path'
datatype pat = WILDCARD
             | PVAR     of name
             | CONPAT   of vcon * pat list
(* <definitions of [[exp]] and [[value]] for \mcl>= *)
type overloading = int ref
type formal = name * tyex
datatype exp 
  = LITERAL    of value
  | VAR        of pathex
  | VCONX      of vcon
  | CASE       of exp * (pat * exp) list   (* XXX pat needs to hold a path *)
  | IFX        of exp * exp * exp (* could be syntactic sugar for CASE *)
  | SET        of name * exp
  | WHILEX     of exp * exp
  | BEGIN      of exp list
  | APPLY      of exp * exp list * overloading
  | LETX       of let_kind * (name * exp) list * exp
  | LETRECX    of ((name * tyex) * exp) list * exp
  | LAMBDA     of formal list * exp
  | MODEXP     of (name * exp) list    (* from body of a generic module *)
  | ERRORX     of exp list
  | EXP_AT     of srcloc * exp
and let_kind = LET | LETSTAR
(* <definitions of [[exp]] and [[value]] for \mcl>= *)
and value
  = CONVAL of vcon * value ref list
  | SYM  of name
  | NUM  of int
  | MODVAL of value ref env
  | CLOSURE   of lambda * value ref env
  | PRIMITIVE of primop
  | ARRAY     of value array
 withtype lambda = name list * exp
      and primop = value list -> value
(* Exp and value representations                *)
(*                                              *)
(* <boxed values 176>=                          *)
type value = value
val unitVal = SYM "unit"  (* XXX placeholder *)
(* <definition of [[def]] for \mcl>=            *)
type modtyex = modtyx
datatype baredef = VAL    of name * exp
              | VALREC   of name * tyex * exp
              | EXP      of exp
                                                           (* not in a module *)
              | QNAME    of pathex
                                                           (* not in a module *)
              | DEFINE   of name * tyex * (formal list * exp)
              | TYPE     of name * tyex
              | DATA     of data_def
              | OVERLOAD of pathex list
              | MODULE   of name * moddef
              | GMODULE  of name * (name * modtyex) list * moddef
              | MODULETYPE of name * modtyex
                                                           (* not in a module *)
and moddef = MPATH       of pathex
           | MPATHSEALED of modtyex * pathex
           | MSEALED     of modtyex * def list
           | MUNSEALED   of def list
  withtype data_def = name * (name * tyex) list
       and def = baredef located
(* Abstract syntax and values                   *)
(*                                              *)
(* <boxed values 136>=                          *)
type exp = exp
(* The definitions of \mcl are the definitions of \nml, *)
(* plus [[DATA]], [[OVERLOAD]], and three       *)
(* module-definition forms. \mcllabeldef        *)
(* <boxed values 136>=                          *)
type def = def
type data_def = data_def
(*<definition of [[implicit_data_def]] for \mcl>*)
(* <definition of [[unit_test]] for explicitly typed languages>= *)
datatype unit_test = CHECK_EXPECT      of exp * exp
                   | CHECK_ASSERT      of exp
                   | CHECK_ERROR       of exp
                   | CHECK_TYPE        of exp * tyex
                   | CHECK_TYPE_ERROR  of def
  | CHECK_MTYPE of pathex * modtyx
(* The differences between [[VAL]] and [[EXP]] are *)
(* subtle: for [[VAL]], the rules of micro-Scheme *)
(* require that we add the name to environment [[rho]] *)
(* before evaluating expression [[e]]. For [[EXP]], we *)
(* don't bind the name [[it]] until after evaluating the *)
(* first top-level expression.                  *)
(* <definition of [[xdef]] (shared)>=           *)
datatype xdef = DEF    of def
              | USE    of name
              | TEST   of unit_test
              | DEFS   of def list  (*OMIT*)
val BugInTypeInference = BugInTypeChecking (* to make \uml utils work *)
(* Practically duplicates uML. Can we share code? *)
(* <definition of [[valueString]] for \mcl>=    *)
fun vconString (PNAME c) = c
  | vconString (PDOT (m, c)) = vconString m ^ "." ^ c
  | vconString (PAPPLY _) = "can't happen! (vcon PAPPLY)"

fun valueString (CONVAL (PNAME "cons", [ref v, ref vs])) = consString (v, vs)
  | valueString (CONVAL (PNAME "'()",  []))      = "()"
  | valueString (CONVAL (c, []))  = vconString c
  | valueString (CONVAL (c, vs))  =
      "(" ^ vconString c ^ " " ^ spaceSep (map (valueString o !) vs) ^ ")"
  | valueString (NUM n      )   = String.map (fn #"~" => #"-" | c => c) (
                                                                 Int.toString n)
  | valueString (SYM v      )   = v
  | valueString (CLOSURE   _)   = "<procedure>"
  | valueString (PRIMITIVE _)   = "<procedure>"
  | valueString (MODVAL _)      = "<module>"
  | valueString (ARRAY a)       =
      "[" ^ spaceSep (map valueString (Array.foldr op :: [] a)) ^ "]"
(* <definition of [[valueString]] for \mcl>=    *)
and consString (v, vs) =
      let fun tail (CONVAL (PNAME "cons", [ref v, ref vs])) = " " ^ valueString
                                                                     v ^ tail vs
            | tail (CONVAL (PNAME "'()", []))       = ")"
            | tail _ =
                raise BugInTypeChecking
                  "bad list constructor (or cons/'() redefined)"
      in  "(" ^ valueString v ^ tail vs
	  end
(* <definition of [[patString]] for \uml\ and \uhaskell ((mcl))>= *)
fun patString WILDCARD    = "_"
  | patString (PVAR x)    = x
  | patString (CONPAT (vcon, []))   = vconString vcon
  | patString (CONPAT (vcon, pats)) = "(" ^ spaceSep (vconString vcon :: map
                                                           patString pats) ^ ")"
(* <definition of [[typeString]] for \mcl\ types>= *)
fun modidentString (MODCON { printName = m, serial = 0 }) = m
  | modidentString (MODCON { printName = m, serial = k }) = m ^ "@{" ^ intString
                                                                         k ^ "}"
  | modidentString (MODTYPLACEHOLDER s) = "<signature: " ^ s ^ ">"

fun pathString' base =
  let fun s (PNAME a) = base a
        | s (PDOT (p, x)) = s p ^ "." ^ x
        | s (PAPPLY (f, args)) =
            String.concat ("(@m " :: s f ::
                           foldr (fn (a, tail) => " " :: s a :: tail) [")"] args
                                                                               )
  in  s
  end

fun pathString (PNAME a) = modidentString a
  | pathString (PDOT (PNAME (MODTYPLACEHOLDER _), x)) = x
  | pathString (PDOT (p, x)) = pathString p ^ "." ^ x
  | pathString (PAPPLY (f, args)) =
      String.concat ("(@m " :: pathString f ::
                     foldr (fn (a, tail) => " " :: pathString a :: tail) [")"]
                                                                           args)

(*val pathString = pathString' modidentString*)
val pathexString : pathex -> string = pathString' snd
(* <definition of [[typeString]] for \mcl\ types>= *)
fun typeString' ps (TYNAME p) = ps p
  | typeString' ps (FUNTY (args, res)) = 
      "(" ^ spaceSep (map (typeString' ps) args) ^ " -> " ^ (typeString' ps) res
                                                                           ^ ")"
  | typeString' ps ANYTYPE = "<any type>"

val typeString = typeString' pathString
val tyexString : tyex -> string = typeString' (pathString' snd)
(* <definition of [[typeString]] for \mcl\ types>= *)
fun mtString (MTEXPORTS []) = "(exports)"
  | mtString (MTEXPORTS comps) = 
      "(exports " ^ spaceSep (map ncompString comps) ^ ")"
  | mtString (MTALLOF  mts) = "(allof " ^ spaceSep (map mtString mts) ^ ")"
  | mtString (MTARROW (args, res)) =
      "(" ^ spaceSep (map modformalString args) ^ " --m-> " ^ mtString res ^ ")"
and modformalString (m, t) = "[" ^ modidentString m ^ " : " ^ mtString t ^ "]"
and ncompString (x, c) =
  case c
    of COMPVAL tau => "[" ^ x ^ " : " ^ typeString tau ^ "]"
     | COMPABSTY _   => "(abstype " ^ x ^ ")"
     | COMPMANTY tau => "(type " ^ x ^ " " ^ typeString tau ^ ")"
     | COMPMOD mt => "(module [" ^ x ^ " : " ^ mtString mt ^ "])"

fun ndecString (x, c) =
  case c
    of ENVVAL tau => "[" ^ x ^ " : " ^ typeString tau ^ "]"
     | ENVMANTY tau => "(type " ^ x ^ " " ^ typeString tau ^ ")"
     | ENVMOD (mt, _) => "(module [" ^ x ^ " : " ^ mtString mt ^ "])"
     | ENVOVLN _ => "<overloaded name " ^ x ^ " ...>"
     | ENVMODTY mt => "(module-type " ^ x ^ " " ^ mtString mt ^ ")"

(* <definition of [[typeString]] for \mcl\ types>= *)
fun mtxString (MTNAMEDX _) = raise BugInTypeChecking "named module, elaborated"
  | mtxString (MTEXPORTSX []) = "(exports)"
  | mtxString (MTEXPORTSX lcomps) = 
      "(exports " ^ spaceSep (map ncompxString lcomps) ^ ")"
  | mtxString (MTALLOFX  mts) = "(allof " ^ spaceSep (map (mtxString o snd) mts)
                                                                           ^ ")"
  | mtxString (MTARROWX (args, res)) =
      "(" ^ spaceSep (map modformalString args) ^ " --m-> " ^ mtxString (snd res
                                                                         ) ^ ")"
and modformalString (m, t) = "[" ^ snd m ^ " : " ^ mtxString (snd t) ^ "]"
and ncompxString (loc, (x, c)) =
  case c
    of DECVAL tau => "[" ^ x ^ " : " ^ tyexString tau ^ "]"
     | DECABSTY   => "(abstype " ^ x ^ ")"
     | DECMANTY tau => "(type " ^ x ^ " " ^ tyexString tau ^ ")"
     | DECMOD mt => "(module [" ^ x ^ " : " ^ mtxString mt ^ "])"
     | DECMODTY mt => "(module-type " ^ x ^ " " ^ mtxString mt ^ ")"
(* <definition of [[typeString]] for \mcl\ types>= *)
fun boolString b = if b then "#t" else "#f"
(* <definition of [[expString]] for \mcl>=      *)
fun stripExpAt (EXP_AT (_, e)) = stripExpAt e
  | stripExpAt e = e

fun expString e =
  let fun bracket s = "(" ^ s ^ ")"
      fun sqbracket s = "[" ^ s ^ "]"
      val bracketSpace = bracket o spaceSep
      fun exps es = map expString es
      fun withBindings (keyword, bs, e) =
        bracket (spaceSep [keyword, bindings bs, expString e])
      and bindings bs = bracket (spaceSep (map binding bs))
      and binding (x, e) = sqbracket (x ^ " " ^ expString e)
      fun formal (x, ty) = sqbracket (x ^ " : " ^ tyexString ty)
      fun tbindings bs = bracket (spaceSep (map tbinding bs))
      and tbinding ((x, tyex), e) = bracket (formal (x, tyex) ^ " " ^ expString
                                                                              e)
      val letkind = fn LET => "let" | LETSTAR => "let*"
  in  case e
        of LITERAL v => valueString v
         | VAR name => pathexString name
         | IFX (e1, e2, e3) => bracketSpace ("if" :: exps [e1, e2, e3])
         | SET (x, e) => bracketSpace ["set", x, expString e]
         | WHILEX (c, b) => bracketSpace ["while", expString c, expString b]
         | BEGIN es => bracketSpace ("begin" :: exps es)
         | APPLY (e, es, _) => bracketSpace (exps (e::es))
         | LETX (lk, bs, e) => bracketSpace [letkind lk, bindings bs, expString
                                                                              e]
         | LETRECX (bs, e) => bracketSpace ["letrec", tbindings bs, expString e]
         | LAMBDA (xs, body) => bracketSpace ("lambda" :: map formal xs @ [
                                                                expString body])
         | VCONX vcon => vconString vcon
         | CASE (e, matches) =>
             let fun matchString (pat, e) = sqbracket (spaceSep [patString pat,
                                                                   expString e])
             in  bracketSpace ("case" :: expString e :: map matchString matches)
             end
         | MODEXP components => bracketSpace ("modexp" :: map binding components
                                                                               )
         | ERRORX es => bracketSpace ("error" :: exps es)
         | EXP_AT (_, e) => expString e
  end
(* <definition of [[expString]] for \mcl>=      *)
fun defString d =
  let fun bracket s = "(" ^ s ^ ")"
      val bracketSpace = bracket o spaceSep
      fun sq s = "[" ^ s ^ "]"
      val sqSpace = sq o spaceSep
      fun formal (x, t) = "[" ^ x ^ " : " ^ tyexString t ^ "]"
  in  case d
        of EXP e         => expString e
         | VAL    (x, e) => bracketSpace ["val",     x, expString e]
         | VALREC (x, t, e) =>
             bracketSpace ["val-rec", sqSpace [x, ":", tyexString t], expString
                                                                              e]
         | DEFINE (f, ty, (formals, body)) =>
             bracketSpace ["define", tyexString ty, f,
                           bracketSpace (map formal formals), expString body]
         | QNAME p => pathexString p
         | TYPE (t, tau) => bracketSpace ["type", t, tyexString tau]
         | DATA (t, _) => bracketSpace ["data", t, "..."]
         | OVERLOAD paths => bracketSpace ("overload" :: map pathexString paths)
         | MODULE (m, _) => bracketSpace ["module", m, "..."]
         | GMODULE (m, _, _) => bracketSpace ["generic-module", m, "..."]
         | MODULETYPE (t, mt) => bracketSpace ["module-type", t, "..."]
  end

(* <utility functions on \uml\ values ((mcl))>= *)
fun primitiveEquality (v, v') =
  let fun noFun () = raise RuntimeError "compared functions for equality"
  in  case (v, v')
        of (NUM  n1,  NUM  n2)  => (n1 = n2)
         | (SYM  v1,  SYM  v2)  => (v1 = v2)
         | (CONVAL (vcon, vs), CONVAL (vcon', vs')) =>
             vcon = vcon' andalso ListPair.allEq primitiveEquality (map ! vs,
                                                                      map ! vs')
         | (CLOSURE   _, _) => noFun ()
         | (PRIMITIVE _, _) => noFun ()
         | (_, CLOSURE   _) => noFun ()
         | (_, PRIMITIVE _) => noFun ()
         | _ => raise BugInTypeInference
                        ("compared incompatible values " ^ valueString v ^
                                                                       " and " ^
                         valueString v' ^ " for equality")
  end
val testEqual = primitiveEquality
(*  1. Define function [[all-pairs?]], which tests its *)
(*  first argument on all pairs of values taken from *)
(*  its second two arguments. Here are some more *)
(*  example calls:                              *)

(* <utility functions on \uml\ values ((mcl))>= *)
fun embedList []      = CONVAL (PNAME "'()", [])
  | embedList (v::vs) = CONVAL (PNAME "cons", [ref v, ref (embedList vs)])
(* <utility functions on \uml\ values ((mcl))>= *)
fun embedBool b = CONVAL (PNAME (if b then "#t" else "#f"), [])
fun bool (CONVAL (PNAME "#t", [])) = true
  | bool _                         = false


(*****************************************************************)
(*                                                               *)
(*   SUPPORT FOR OPERATOR OVERLOADING IN \MCL                    *)
(*                                                               *)
(*****************************************************************)

(* <support for operator overloading in \mcl>=  *)
val notOverloadedIndex = ~1
val overloadTable = "overloaded operators"
                                         (* name cannot appear in source code *)
val emptyOverloadTable = Array.tabulate (10, fn _ => SYM
                                              "<empty entry in overload table>")
fun overloadCell rho =
  find (overloadTable, rho) handle NotFound _ => raise InternalError
                                                        "missing overload table"
fun overloadedAt (rho, i) =
  case overloadCell rho
    of ref (ARRAY a) => Array.sub (a, i)
     | _ => raise InternalError "representation of overload table"
local
  val next = ref 0
in
  fun nextOverloadedIndex () = !next before next := !next + 1
end

fun overloadedPut (i, v, rho) =
  let val cell = overloadCell rho
      val a  = case cell of ref (ARRAY a) => a | _ => raise InternalError
                                                         "rep of overload table"
      val a' = if i >= Array.length a then
                 let val n = 2 * Array.length a
                     val a' = Array.tabulate (n, fn j => if j < n then Array.sub
                                                                  (a, j) else v)
                     val _ = cell := ARRAY a'
                 in  a'
                 end
               else
                 a
  in  Array.update (a', i, v)
  end



(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS AND PARSING FOR \MCL, PROVIDING [[FILEXDEFS]] AND [[STRINGSXDEFS]] *)
(*                                                               *)
(*****************************************************************)

(* Lexical analysis and parsing                 *)
(*                                              *)
(* [*]                                          *)
(* <lexical analysis and parsing for \mcl, providing [[filexdefs]] and [[stringsxdefs]]>= *)
(* <lexical analysis for {\mcl}>=               *)
datatype pretoken = QUOTE
                  | INT      of int
                  | RESERVED of string
                  | DOTTED   of string * string list
                               (* name, possibly followed by dotted selection *)
                  | DOTNAMES of string list (* .x.y and so on *)
type token = pretoken plus_brackets
(* <lexical analysis for {\mcl}>=               *)
fun pretokenString (QUOTE)      = "'"
  | pretokenString (INT  n)     = intString n
  | pretokenString (DOTTED (s, ss))  = separate ("", ".") (s::ss)
  | pretokenString (DOTNAMES ss)= (concat o map (fn s => "." ^ s)) ss
  | pretokenString (RESERVED x) = x
val tokenString = plusBracketsString pretokenString
(* <lexical analysis for {\mcl}>=               *)
local
  val isDelim = fn c => isDelim c orelse c = #"."
  (* <functions used in all lexers>=              *)
  fun noneIfLineEnds chars =
    case streamGet chars
      of NONE => NONE (* end of line *)
       | SOME (#";", cs) => NONE (* comment *)
       | SOME (c, cs) => 
           let val msg = "invalid initial character in `" ^
                         implode (c::listOfStream cs) ^ "'"
           in  SOME (ERROR msg, EOS)
           end
  (* If the lexer doesn't recognize a bracket, quote mark, *)
  (* integer, or other atom, we're expecting the line to *)
  (* end. The end of the line may present itself as the *)
  (* end of the input stream or as a stream of characters *)
  (* beginning with a semicolon, which marks a comment. *)
  (* If we encounter any other character, something has *)
  (* gone wrong. (The polymorphic type of         *)
  (* [[noneIfLineEnds]] provides a subtle but powerful *)
  (* hint that no token can be produced; the only possible *)
  (* outcomes are that nothing is produced, or the lexer *)
  (* detects an error.) [*]                       *)
  (* <boxed values 29>=                           *)
  val _ = op noneIfLineEnds : 'a lexer
  val reserved = 
    [ (* <words reserved for \mcl\ types>=            *)
      "->", ":"
    , (* <words reserved for \mcl\ expressions>=      *)
      "@m", "if", "&&", "||", "set", "let", "let*", "letrec", "case", "lambda",
      "val", "set", "while", "begin", "error",
      "when", "unless", "assert"
      (* , "assert" *)
    , (* <words reserved for \mcl\ definitions>=      *)
      ":", 
      "val", "define", "exports", "allof", "module-type", "module", "--m->",
      "generic-module", "unsealed-module", "type", "abstype", "data",
      "record-module", "record-module-type",
      "use", "check-expect", "check-assert",
      "check-error", "check-type", "check-type-error",
      "check-module-type",
      "overload"
    ]
  fun isReserved x = member x reserved
  datatype part = DOT | NONDELIMS of string
  val nondelims = (NONDELIMS o implode) <$> many1 (sat (not o isDelim) one)
  val dot       = DOT <$ eqx #"." one
  fun dottedNames things =
    let exception Can'tHappen
        fun preDot (ss', DOT :: things)    = postDot (ss', things)
          | preDot (ss', nil)              = OK (rev ss')
          | preDot (ss', NONDELIMS _ :: _) = raise Can'tHappen
        and postDot (ss', DOT :: _) = ERROR
                             "A qualified name may not contain consecutive dots"
          | postDot (ss', nil)      = ERROR
                                       "A qualified name may not end with a dot"
          | postDot (ss', NONDELIMS s :: things) =
              if isReserved s then
                ERROR ("reserved word '" ^ s ^ "' used in qualified name")
              else
                preDot (s :: ss', things)
    in  case things
          of NONDELIMS s :: things => preDot  ([], things) >>=+ curry DOTTED s
           | DOT         :: things => postDot ([], things) >>=+ DOTNAMES
           | [] => ERROR "Lexer is broken; report to nr@cs.tufts.edu"
    end

  fun reserve (token as DOTTED (s, [])) =
        if isReserved s then
          RESERVED s
        else
          token
    | reserve token = token

in
  val mclToken =
    whitespace *>
    bracketLexer (  QUOTE   <$  eqx #"'" one
                <|> INT     <$> intToken isDelim
                <|> reserve <$> (dottedNames <$>! many1 (nondelims <|> dot))
                <|> noneIfLineEnds
                 )
(* <boxed values 191>=                          *)
val _ = op mclToken : token lexer
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

end
fun 'a parseAt at p = at <$> @@ p
(* <parsers for \mcl\ tokens>=                  *)
type 'a parser = (token, 'a) polyparser
val pretoken  = (fn (PRETOKEN t)=> SOME t  | _ => NONE) <$>? token : pretoken
                                                                          parser
val quote     = (fn (QUOTE)     => SOME () | _ => NONE) <$>? pretoken
val int       = (fn (INT   n)   => SOME n  | _ => NONE) <$>? pretoken
val name  = (fn (DOTTED (x, []))   => SOME x  | _ => NONE) <$>? pretoken
val dotted  = (fn (DOTTED (x, xs))   => SOME (x, xs)  | _ => NONE) <$>? pretoken
val dotnames = (fn (DOTNAMES xs)  => SOME xs | _ => NONE) <$>? pretoken
val reserved = (fn RESERVED r => SOME r | _ => NONE) <$>? pretoken
val any_name = name

val arrow = eqx "->" reserved <|> eqx "--m->" reserved

val showErrorInput = (fn p => showErrorInput tokenString p)
val booltok = pzero  (* depressing *)
(* A token that presents as a name is one of the *)
(* following: an arrow, a value constructor, a value *)
(* variable, or a type name. First the predicates: *)
(* <parsers for \uml\ value constructors and value variables>= *)
fun isVcon x =
  let val first = String.sub (x, 0)
  in  x = "cons" orelse x = "'()" orelse
      Char.isUpper first orelse first = #"#" orelse
      String.isPrefix "make-" x
  end
fun isVvar x = x <> "->" andalso not (isVcon x)
(* And now the parsers. A value constructor may be not *)
(* only a suitable name but also a Boolean literal or *)
(* the empty list.                              *)

(* <parsers for \uml\ value constructors and value variables>= *)
val arrow = sat (fn n => n = "->") any_name
val vvar  = sat isVvar any_name
val tyname = vvar
val vcon  = 
  let fun isEmptyList (left, right) = notCurly left andalso snd left = snd right
      val boolcon  = (fn p => if p then "#t" else "#f") <$> booltok
  in  boolcon <|> sat isVcon any_name <|>
      "'()" <$ quote <* sat isEmptyList (pair <$> left <*> right)
  end
(* <parsers and parser builders for formal parameters and bindings>= *)
fun formalsOf what name context = 
  nodups ("formal parameter", context) <$>! @@ (bracket (what, many name))

fun bindingsOf what name exp =
  let val binding = bracket (what, pair <$> name <*> exp)
  in  bracket ("(... " ^ what ^ " ...) in bindings", many binding)
  end

fun distinctBsIn bindings context =
  let fun check (loc, bs) =
        nodups ("bound name", context) (loc, map fst bs) >>=+ (fn _ => bs)
  in  check <$>! @@ bindings
  end
(* The next step up is syntactic elements used in *)
(* multiple Scheme-like languages. Function [[formals]] *)
(* parses a list of formal parameters. If the formal *)
(* parameters contain duplicates, it's treated as a *)
(* syntax error. Function [[bindings]] produces a list *)
(* of bindings suitable for use in [[let*]] expressions. *)
(* For [[let]] and [[letrec]] expressions, which do not *)
(* permit multiple bindings to the same name, use *)
(* [[distinctBsIn]].                            *)
(* <boxed values 30>=                           *)
val _ = op formalsOf  : string -> name parser -> string -> name list parser
val _ = op bindingsOf : string -> 'x parser -> 'e parser -> ('x * 'e) list
                                                                          parser
val _ = op distinctBsIn : (name * 'e) list parser -> string -> (name * 'e) list
                                                                          parser
(* <parsers and parser builders for formal parameters and bindings>= *)
fun recordFieldsOf name =
  nodups ("record fields", "record definition") <$>!
                                    @@ (bracket ("(field ...)", many name))
(* Record fields also may not contain duplicates. *)
(* <boxed values 31>=                           *)
val _ = op recordFieldsOf : name parser -> name list parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <parsers and parser builders for formal parameters and bindings>= *)
fun kw keyword = 
  eqx keyword any_name
fun usageParsers ps = anyParser (map (usageParser kw) ps)
(* We parse any keyword as the name represented by the *)
(* same string as the keyword. And using the keyword *)
(* parser, we can string together ``usage'' parsers. *)
(* <boxed values 32>=                           *)
val _ = op kw : string -> string parser
val _ = op usageParsers : (string * 'a parser) list -> 'a parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

val tyvar = sat (fn _ => false) name  (* must have a monomorphic type *)
(* <parser builders for typed languages>=       *)
val distinctTyvars = 
  nodups ("quantified type variable", "forall") <$>! @@ (many tyvar)

fun arrowsOf conapp funty =
  let fun arrows []              [] = ERROR "empty type ()"
        | arrows (tycon::tyargs) [] = OK (conapp (tycon, tyargs))
        | arrows args            [rhs] =
            (case rhs of [result] => OK (funty (args, result))
                       | []       => ERROR "no result type after function arrow"
                       | _        => ERROR
                                   "multiple result types after function arrow")
        | arrows args (_::_::_) = ERROR "multiple arrows in function type"
  in  arrows
  end
(* <parser builders for typed languages>=       *)
fun typedFormalOf name colon ty =
      bracket ("[x : ty]", pair <$> name <* colon <*> ty)
fun typedFormalsOf name colon ty context = 
  let val formal = typedFormalOf name colon ty
  in  distinctBsIn (bracket("(... [x : ty] ...)", many formal)) context
  end                            
(* <boxed values 291>=                          *)
val _ = op typedFormalsOf : string parser -> 'b parser -> 'a parser -> string ->
                                                       (string * 'a) list parser
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun kw keyword = eqx keyword reserved
fun usageParsers ps = anyParser (map (usageParser kw) ps)
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun getkeyword (usage:string) = (one *> one *> one) (lexLineWith mclToken usage)
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun wrap  what = wrapAround tokenString what
fun wrap_ what p = p
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun showParsed show p =
  let fun diagnose a = (eprintln ("parsed " ^ show a); a)
  in  diagnose <$> p
  end

fun showParsed_ show p = p
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun bracketOrFail (_, p) =
  let fun matches (_, l) a (loc, r) =
        if l = r then OK a
        else errorAt (leftString l ^ " closed by " ^ rightString r) loc
  in  matches <$> left <*> p <*>! right
  end
(* <parsers and [[xdef]] streams for \mcl>=     *)

fun addDots p xs = foldl (fn (x, p) => PDOT (p, x)) p xs
fun dotsPath (loc, (x, xs)) = addDots (PNAME (loc, x)) xs
fun path tokens =
  ( dotsPath <$> @@ dotted
  <|>
      addDots <$>
        bracketKeyword
           (kw "@m", "(@m name path ...)", curry PAPPLY <$> (PNAME <$> @@ name)
                                                                  <*> many path)
              <*> (dotnames <|> pure [])
  ) tokens

fun mkTyex br tokens =
  let val ty = wrap_ "inner type" (showErrorInput (mkTyex br))
      fun arrows []              [] = ERROR "empty type ()"
        | arrows (tycon::tyargs) [] = ERROR "missing @@ or ->"
        | arrows args            [rhs] =
            (case rhs of [result] => OK (FUNTY (args, result))
                       | []       => ERROR "no result type after function arrow"
                       | _        => ERROR
                                   "multiple result types after function arrow")
        | arrows args (_::_::_) = ERROR "multiple arrows in function type"
      val parser =
            TYNAME <$> path
        <|> br
               ( "(ty ty ... -> ty)"
               ,  arrows <$> many ty <*>! many (kw "->" *> many ty)
               )
  in  parser (* curry TYEX_AT () <$> @@ parser *)
  end tokens
val tyex = wrap_ "tyex" (mkTyex (showErrorInput o bracket)) : tyex parser
val liberalTyex = mkTyex bracketOrFail
(* <parsers and [[xdef]] streams for \mcl>=     *)
val bare_vcon = vcon
fun dottedVcon (x, xs) = addDots (PNAME x) xs
fun vconLast (PDOT (_, x)) = x
  | vconLast (PNAME x) = x
  | vconLast (PAPPLY _) = raise InternalError "application vcon"
val vcon =  sat (isVcon o vconLast) (dottedVcon <$> dotted) 
        <|> PNAME <$> bare_vcon
        <|> (fn (loc, (x, xs)) => errorAt (
                                   "Expected value constructor, but got name " ^
                                           foldl (fn (x, p) => p ^ "." ^ x) x xs
                                                                          ) loc)
            <$>! @@ dotted

fun pattern tokens =  (
                WILDCARD    <$  eqx "_" vvar
      <|>       PVAR        <$> vvar
      <|> curry CONPAT      <$> vcon <*> pure []
      <|> bracket ( "(C x1 x2 ...) in pattern"
                  , curry CONPAT <$> vcon <*> many pattern
                  )
       ) tokens
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun badReserved r = 
  ERROR ("reserved word '" ^ r ^ "' where name was expected")

fun quoteName "#f" = CONVAL (PNAME "#f", [])
  | quoteName "#t" = CONVAL (PNAME "#t", [])
  | quoteName s    = SYM s

fun quotelit tokens = (
         quoteName <$> name
    <|>  NUM <$> int
    <|>  (ARRAY o Array.fromList) <$> bracket ("(literal ...)", many quotelit)
    ) tokens

val atomicExp =  VAR           <$> path
             <|> badReserved <$>! reserved
             <|> dotnames <!> "a qualified name may not begin with a dot"
             <|> LITERAL <$> NUM <$> int
             <|> VCONX <$> vcon
             <|> quote *> (LITERAL <$> quotelit)

fun bindTo exp = bracket ("[x e]", pair <$> name <*> exp)
(* <parsers and [[xdef]] streams for \mcl>=     *)
val formal = bracket ("[x : ty]", pair <$> name <* kw ":" <*> tyex)
val lformals = bracket ("([x : ty] ...)", many formal)
fun nodupsty what (loc, xts) = nodups what (loc, map fst xts) >>=+ (fn _ => xts)

                                                  (* error on duplicate names *)


fun smartBegin [e] = e
  | smartBegin es = BEGIN es

fun exptable exp =
  let val zero = LITERAL (NUM 0)
      fun single binding = [binding]
      fun badReserved words =
        let fun die w = ERROR ("while trying to parse an expression, I see " ^
                               "reserved word " ^ w ^

                            "... did you misspell a statement keyword earlier?")
        in  die <$>! sat (fn w => member w words) (left *> reserved)
        end
      val bindings = bindingsOf "[x e]" name exp
      val tbindings = bindingsOf "[x : ty]" formal exp
      val dbs       = distinctBsIn bindings

      val choice   = bracket ("[pattern exp]", pair <$> pattern <*> exp)
      val body = smartBegin <$> many1 exp
      val nothing = pure (BEGIN [])

      fun cand [e] = e
        | cand (e::es) = IFX (e, cand es, LITERAL (embedBool false))
        | cand [] = raise InternalError "parsing &&"

      fun cor [e] = e
        | cor (e::es) = IFX (e, LITERAL (embedBool true), cor es)
        | cor [] = raise InternalError "parsing ||"

     fun lambda (xs : (name * tyex) list located) exp =
       nodupsty ("formal parameter", "lambda") xs >>=+ (fn xs => LAMBDA (xs, exp
                                                                              ))

  in usageParsers
     [ ("(if e1 e2 e3)",            curry3 IFX          <$> exp <*> exp <*> exp)
     , ("(when e1 e ...)",          curry3 IFX          <$> exp <*> body <*>
                                                                        nothing)
     , ("(unless e1 e ...)",        curry3 IFX          <$> exp <*> nothing <*>
                                                                           body)
     , ("(set x e)",                curry  SET          <$> name <*> exp)
     , ("(while e body)",           curry  WHILEX       <$> exp  <*> body)
     , ("(begin e ...)",                   BEGIN        <$> many exp)
     , ("(error e ...)",                   ERRORX       <$> many exp)
     , ("(let (bindings) body)",    curry3 LETX LET     <$> dbs "let"    <*>
                                                                           body)
     , ("(let* (bindings) body)",   curry3 LETX LETSTAR <$> bindings     <*>
                                                                           body)
     , ("(letrec (typed-bindings) body)", curry LETRECX <$> tbindings <*> body)
     , ("(case exp (pattern exp) ...)", curry CASE <$> exp <*> many choice)
     , ("(lambda ([x : ty] ...) body)", lambda <$> @@ (lformals : (name * tyex)
                                                         list parser) <*>! body)
     , ("(&& e ...)",               cand <$> many1 exp)
     , ("(|| e ...)",               cor  <$> many1 exp)
     , ("(assert e)",
        curry3 IFX <$> exp <*> nothing <*> pure (ERRORX [LITERAL (SYM
                                                         "assertion-failure")]))
     , ("(quote sx)",               LITERAL <$> quotelit)
     ]
    <|> badReserved [(* <words reserved for \mcl\ types>=            *)
                     "->", ":",
                     (* <words reserved for \mcl\ definitions>=      *)
                     ":", 
                     "val", "define", "exports", "allof", "module-type",
                                                              "module", "--m->",
                     "generic-module", "unsealed-module", "type", "abstype",
                                                                         "data",
                     "record-module", "record-module-type",
                     "use", "check-expect", "check-assert",
                     "check-error", "check-type", "check-type-error",
                     "check-module-type",
                     "overload"]
  end
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun applyNode f args = APPLY (f, args, ref notOverloadedIndex)
fun exp tokens = showParsed_ expString (parseAt EXP_AT replExp) tokens
and replExp tokens = showErrorInput 
       (  (* component here only if type with reserved word *)
          atomicExp
      <|> exptable exp
      <|> leftCurly <!> "curly brackets are not supported"
      <|> left *> right <!> "empty application"
      <|> bracket("function application", applyNode <$> exp <*> many exp)
  ) tokens

(* NO COMPONENTS AT TOP LEVEL!                  *)
(* <boxed values 192>=                          *)
val _ = op exptable : exp parser -> exp parser
val _ = op exp      : exp parser

val replExp = showParsed_ expString (parseAt EXP_AT replExp)
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun formalWith whatTy aTy =
  bracket ("[x : " ^ whatTy ^ "]", pair <$> name <* kw ":" <*> aTy)

val formal = formalWith "ty" tyex

fun prightmap f (x, a) = (x, f a)
fun crightmap f x a = (x, f a)

fun recordModuleType tyname (loc, formals : (name * tyex) list) =
  let val t = TYNAME (PNAME (loc, tyname))
      val unitty  = TYNAME (PDOT (PNAME (loc, "Unit"), "t"))
      val conty = FUNTY (map snd formals, t)
      fun getterty (x, tau) = (loc, (x, DECVAL (FUNTY ([t], tau))))
      fun setname x = "set-" ^ x ^ "!"
      fun setterty (x, tau) = (loc, (setname x, DECVAL(FUNTY ([t, tau], unitty))
                                                                              ))
      val exports = (loc, (tyname, DECABSTY)) :: (loc, ("make", DECVAL conty))
                                                                              ::
                    map getterty formals @ map setterty formals
  in  MTEXPORTSX exports
  end

fun recordModule (loc, name) tyname (formals : (name * tyex) list) =
  let val t = TYNAME (PNAME (loc, tyname))
      val vcon = "make-" ^ name ^ "." ^ tyname
      val conpat = CONPAT (PNAME vcon, map (PVAR o fst) formals)
      val conname = name ^ ".make"
      fun setname x = "set-" ^ x ^ "!"
      fun var x = VAR (PNAME (loc, x))
      val conval =
        LAMBDA (formals, APPLY (VCONX (PNAME vcon), map (var o fst) formals, ref
                                                            notOverloadedIndex))
      fun getter n =
        (LAMBDA ([("r", t)],
                 CASE (var "r", [(conpat, var (fst (List.nth (formals, n))))])))
      fun setter n = 
        (LAMBDA ([("the record", t), ("the value", snd (List.nth (formals, n)))]
                                                                               ,
                 CASE (var "the record",
                       [(conpat, SET (fst (List.nth (formals, n)), var
                                                               "the value"))])))
      val modty = recordModuleType tyname (loc, formals)

      fun prim (x, f) = VAL (x, f)
      val indices = List.tabulate (length formals, id)
      val components =
        DATA (tyname, [(vcon, FUNTY (map snd formals, t))]) ::
        prim ("make", conval) ::
        ListPair.mapEq (fn ((x,_), i) => prim (x, getter i)) (formals, indices)
                                                                               @
        ListPair.mapEq (fn ((x,_), i) => prim (setname x, setter i)) (formals,
                                                                        indices)
  in  MODULE (name, MSEALED (modty, map (fn d => (loc, d)) components))
  end


fun decl tokens =
  (  usageParsers
       [ ("(abstype t)",          pair <$> name <*> pure DECABSTY)
       , ("(type t ty)",          crightmap DECMANTY  <$> name <*> tyex)
       , ("(module [A : modty])", prightmap DECMOD <$> modformal)
       ]
 <|> prightmap DECVAL <$> formal
  )
  tokens
and locmodformal tokens =
  bracket ("[M : modty]", pair <$> @@ name <* kw ":" <*> @@ modtype) tokens
and modformal tokens =
  ((fn (x, t) => (snd x, snd t)) <$> locmodformal) tokens
and modtype tokens = (
  usageParsers
  [ ("(exports component...)", MTEXPORTSX <$> many (@@ decl))
  , ("(allof module-type...)",  MTALLOFX    <$> many (@@ modtype))
  , ("(record-module-type t ([x : ty] ...))", recordModuleType <$> name <*> @@
                                                                       lformals)
  ] 
  <|> MTNAMEDX <$> name
  <|> bracket ("([A : modty] ... --m-> modty)",
               curry MTARROWX <$> many locmodformal <*> kw "--m->" *> @@ modtype
                                                                               )
  ) tokens
(* <boxed values 193>=                          *)
val _ = op decl : (name * decl) parser
val _ = op locmodformal : (name located * modtyex located) parser
val _ = op modformal    : (name * modtyex) parser
val _ = op modtype      : modtyex parser
(* <parsers and [[xdef]] streams for \mcl>=     *)
val tyex : tyex parser = tyex
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun wantedVcon (loc, x) = errorAt ("expected value constructor, but got name " ^
                                                                          x) loc
fun wantedVvar (loc, x) = errorAt (
                   "expected variable name, but got value constructor " ^ x) loc

val vvar  = sat isVvar name
val vcon  = 
  let fun isEmptyList (left, right) = notCurly left andalso snd left = snd right
      val boolcon  = (fn p => if p then "#t" else "#f") <$> booltok
  in  boolcon <|> sat isVcon name <|>
      "'()" <$ quote <* sat isEmptyList (pair <$> left <*> right)
  end

val (vcon, vvar) = ( vcon <|> wantedVcon <$>! @@ vvar
                   , vvar <|> wantedVvar <$>! @@ vcon
                   )




(* <parsers and [[xdef]] streams for \mcl>=     *)
val defFwd    = ref (forward "def" : def parser)
fun def arg    = !defFwd arg

fun def tokens =
  let val returnTypes = bracket("[ty ...]", many tyex) <|> pure []
  in  showErrorInput (!defFwd)
  end tokens

val def = wrap_ "def" def : def parser

val defbasic : baredef parser = 
  let (* parser for binding to names *)
      val formals = lformals : (name * tyex) list parser
  (*    val formals = vvarFormalsIn "define" *)

      (* parsers for clausal definitions, a.k.a. define* *)
(*
      val lhs = bracket ("(f p1 p2 ...)", pair <$> vvar <*> many pattern)
      val clause =
        bracket ("[(f p1 p2 ...) e]",
                 (fn (f, ps) => fn e => (f, (ps, e))) <$> lhs <*> exp)
*)
      (* definition builders used in all parsers *)
      fun flipPair tx c = (c, tx)


      (* definition builders that expect to bind names *)
      fun define tau f formals body =
        nodupsty ("formal parameter", "definition of function " ^ f) formals
                                                                            >>=+
          (fn xts => DEFINE (f, tau, (xts, body)))
      fun definestar _ = ERROR "define* is left as an exercise"
      val tyname = name
        
      fun valrec (x, tau) e = VALREC (x, tau, e)

      fun sealedWith f (m : name, mt : modtyex) rhs = (m, f (mt, rhs))

      val conTy = typedFormalOf vcon (kw ":") tyex

      val body = smartBegin <$> many1 exp

  in  usageParsers
      [ ("(define type f (args) body)",
                                      define <$> tyex <*> name <*> @@ lformals
                                                                      <*>! body)
      , ("(val x e)",                 curry VAL <$> vvar <*> exp)
      , ("(val-rec [x : type] e)",    valrec <$> formal <*> exp)

      , ("(data t [vcon : ty] ...)",
         wrap_ "data definition" (curry DATA <$> tyname <*> many conTy))
      , ("(type t ty)",           curry TYPE <$> name <*> tyex)
      , ("(module-type T modty)", curry MODULETYPE <$> name <*> modtype)
      , ("(module M path) or (module [M : T] path/defs)",
            MODULE <$> (  (pair <$> name <*> MPATH <$> path : (name * moddef)
                                                                         parser)
                      <|> (sealedWith MPATHSEALED <$> modformal <*> path : (name
                                                               * moddef) parser)
                      <|> (sealedWith MSEALED <$> modformal <*> many def : (name
                                                               * moddef) parser)
                       ))

      , ("(generic-module [M : T] defs)",
            let fun strip ((_, m), (_, t)) = (m, t)
                fun gen ((loc, M), (loc', T)) defs =
                  case T
                    of MTARROWX (formals, result) =>
                         OK (GMODULE (M, map strip formals, MSEALED (snd result,
                                                                         defs)))
                     | _ => ERROR ("at " ^ srclocString loc' ^
                                                           ", generic module " ^
                                   M ^ " does not have an arrow type")
            in   gen <$> locmodformal <*>! many def
            end)
      , ("(unsealed-module M defs)", 
            MODULE <$> (crightmap MUNSEALED <$> name <*> many def))
      , ("(record-module M t ([x : ty] ...))",
            recordModule <$> @@ name <*> name <*> formals)
      , ("(overload qname ...)", OVERLOAD <$> many path)
      ]
     <|> QNAME <$> path
     <|> EXP <$> exp : baredef parser
  end

val _ = defFwd := @@ defbasic
(* <boxed values 194>=                          *)
val _ = op def : def parser

(* <parsers and [[xdef]] streams for \mcl>=     *)
val testtable = usageParsers
  [ ("(check-expect e1 e2)",          curry CHECK_EXPECT     <$> exp <*> exp)
  , ("(check-assert e)",                    CHECK_ASSERT     <$> exp)
  , ("(check-error e)",                     CHECK_ERROR      <$> exp)
  , ("(check-type e tau)",            curry CHECK_TYPE       <$> exp <*> tyex)
  , ("(check-type-error e)",                CHECK_TYPE_ERROR <$> def)
  , ("(check-module-type M T)",       curry CHECK_MTYPE      <$> path <*>
                                                                        modtype)
  ]
(* <parsers and [[xdef]] streams for \mcl>=     *)
fun filenameOfDotted (x, xs) = separate ("", ".") (x :: xs) 
val xdeftable = usageParsers
  [ ("(use filename)", (USE o filenameOfDotted) <$> dotted)
  ]
(* <parsers and [[xdef]] streams for \mcl>=     *)
val xdef =  TEST <$> testtable
        <|>          xdeftable
        <|> DEF <$>  def
        <|> badRight "unexpected right bracket"
        <?> "definition"
(* <parsers and [[xdef]] streams for \mcl>=     *)
val xdefstream = 
  interactiveParsedStream (mclToken, xdef)
(* <shared definitions of [[filexdefs]] and [[stringsxdefs]]>= *)
fun filexdefs (filename, fd, prompts) = xdefstream (filename, filelines fd,
                                                                        prompts)
fun stringsxdefs (name, strings) = xdefstream (name, streamOfList strings,
                                                                      noPrompts)
(* Streams of extended definitions              *)
(*                                              *)
(* Every language has its own parser, called    *)
(* [[xdefstream]], which converts a stream of lines to a *)
(* stream of [[xdef]]s. But as in \cref         *)
(* cinterps.shared-xdef-streams, the convenience *)
(* functions [[filexdefs]] and [[stringsxdefs]] are *)
(* shared.                                      *)
(* <boxed values 228>=                          *)
val _ = op xdefstream   : string * line stream     * prompts -> xdef stream
val _ = op filexdefs    : string * TextIO.instream * prompts -> xdef stream
val _ = op stringsxdefs : string * string list               -> xdef stream

(*<\mcl's overloaded operators>*)


(*****************************************************************)
(*                                                               *)
(*   ENVIRONMENTS FOR \MCL'S DEFINED NAMES                       *)
(*                                                               *)
(*****************************************************************)

(* Type checking                                *)
(*                                              *)
(* Functions on the static environment          *)
(*                                              *)
(* Looking up values                            *)
(*                                              *)
(* <environments for \mcl's defined names>=     *)
(*
fun whatkind (COMPVAL _) = "a value"
  | whatkind (COMPTY _)  = "an ordinary type"
  | whatkind (COMPOVL _) = "an overloading group"
  | whatkind (COMPMOD _) = "a module"
*)

fun whatcomp (COMPVAL _) = "a value"
  | whatcomp (COMPABSTY _) = "an abstract type"
  | whatcomp (COMPMANTY _) = "a manifest type"
  | whatcomp (COMPMOD _) = "a module"

fun whatdec (ENVVAL _) = "a value"
  | whatdec (ENVMANTY _) = "a manifest type"
  | whatdec (ENVOVLN _) = "an overloaded name"
  | whatdec (ENVMOD _) = "a module"
  | whatdec (ENVMODTY _) = "a module type"

fun bigdec (ENVOVLN taus) = "overloaded at " ^ Int.toString (length taus) ^
                            " : [" ^ commaSep (map typeString taus) ^ "]"
  | bigdec d = whatdec d

fun compString (ENVVAL tau) = "a value of type " ^ typeString tau
  | compString (ENVMANTY tau) = "manifest type " ^ typeString tau
  | compString (ENVOVLN _) = "an overloaded name"
  | compString (ENVMOD (mt, path)) = "module " ^ pathString path ^ " of type " ^
                                                                     mtString mt
  | compString (ENVMODTY _) = "a module type"



(*
fun findModty (t, Gamma) =
  case find (t, Gamma)
    of MODTY mt => mt
     | COMPONENT c =>
         raise TypeError ("Used " ^ t ^ " to name a module type, but " ^ t ^
                          " is " ^ whatkind c)
*)



(*****************************************************************)
(*                                                               *)
(*   TYPE CHECKING FOR {\MCL}                                    *)
(*                                                               *)
(*****************************************************************)

(* Wrapup                                       *)
(*                                              *)
(* <type checking for {\mcl}>=                  *)
(* <[[context]] for a {\mcl} definition>=       *)
datatype context
  = TOPLEVEL
  | INMODULE of path

fun contextDot (TOPLEVEL, name) = PNAME (genmodident name)
                                                     (* XXX key to uniqueness *)
  | contextDot (INMODULE path, name) = PDOT (path, name)

fun contextString TOPLEVEL = "at top level"
  | contextString (INMODULE p) = "in module " ^ pathString p
(* Type-checking modules: generativity of top-level *)
(* definitions                                  *)
(*                                              *)
(* Function [[binding]] can be used only in a known *)
(* context—because if the [[def]] defines a module, *)
(* we need to know the path for every component. *)
(* <boxed values 140>=                          *)
type context = context
val _ = op contextDot : context * name -> path
(* <type equality for \mcl>=                    *)
fun eqType (TYNAME p, TYNAME p') = p = p'
  | eqType (FUNTY (args, res), FUNTY (args', res')) =
      eqTypes (args, args') andalso eqType (res, res')
  | eqType (ANYTYPE, _) = true
  | eqType (_, ANYTYPE) = true
  | eqType _ = false
and eqTypes (taus, tau's) = ListPair.allEq eqType (taus, tau's)
(* A literal is either a bare symbol like x, which is *)
(* satisfied by [[#t]], or it is a two-element list like *)
(* \monobox(not x), which is satisfied by [[#f]]. I can *)
(* avoid a case analysis by observing that in both *)
(* cases, the value that satisfies a literal [[lit]] is *)
(* equal to \monobox(symbol? lit).              *)
(* <boxed values 160>=                          *)
val _ = op eqType  : ty      * ty      -> bool
val _ = op eqTypes : ty list * ty list -> bool
(* <substitutions for \mcl>=                    *)
type rootsubst = (modident * path) list
val idsubst = []
(* <boxed values 161>=                          *)
type rootsubst = rootsubst
val _ = op idsubst : rootsubst
(* <substitutions for \mcl>=                    *)
infix 7 |-->
fun id |--> p = [(id, p)]
(* <boxed values 162>=                          *)
val _ = op |--> : modident * path -> rootsubst
(* <substitutions for \mcl>=                    *)
type tysubst = (path * ty) list
fun associatedWith (x, []) =
      NONE
  | associatedWith (x, (key, value) :: pairs) =
      if x = key then SOME value else associatedWith (x, pairs)

fun hasKey [] x = false
  | hasKey ((key, value) :: pairs) x = x = key orelse hasKey pairs x
(* <boxed values 163>=                          *)
type tysubst = tysubst
val _ = op associatedWith : path * tysubst -> ty option
val _ = op hasKey : tysubst -> path -> bool
(* <substitutions for \mcl>=                    *)
fun pathsubstRoot theta =
  let fun subst (PNAME id) =
            (case List.find (fn (id', p') => id = id') theta
               of SOME (_, p) => p
                | NONE => PNAME id)
        | subst (PDOT (p, x)) = PDOT (subst p, x)
        | subst (PAPPLY (p, ps)) = PAPPLY (subst p, map subst ps)
  in  subst
  end
(* <boxed values 164>=                          *)
val _ = op pathsubstRoot : rootsubst -> path -> path
(* <substitutions for \mcl>=                    *)
fun tysubstRoot theta (TYNAME p)          = TYNAME (pathsubstRoot theta p)
  | tysubstRoot theta (FUNTY (args, res)) =
      FUNTY (map (tysubstRoot theta) args, tysubstRoot theta res)
  | tysubstRoot theta ANYTYPE = ANYTYPE
(* <boxed values 165>=                          *)
val _ = op tysubstRoot : rootsubst -> ty -> ty
(* <substitutions for \mcl>=                    *)
fun dom theta = map (fn (a, _) => a) theta
fun compose (theta2, theta1) =
  let val domain  = union (dom theta2, dom theta1)
      val replace = pathsubstRoot theta2 o pathsubstRoot theta1 o PNAME
  in  map (fn a => (a, replace a)) domain
  end
(* <boxed values 166>=                          *)
val _ = op dom     : rootsubst -> modident set
val _ = op compose : rootsubst * rootsubst -> rootsubst
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <substitutions for \mcl>=                    *)
fun bsubstRoot s = 
  map (fn (x, a) => (x, s a))

fun mtsubstRoot theta =
  let fun s (MTEXPORTS comps)     = MTEXPORTS (bsubstRoot (compsubstRoot theta)
                                                                          comps)
        | s (MTALLOF mts)         = MTALLOF (map s mts)
        | s (MTARROW (args, res)) = MTARROW (bsubstRoot s args, s res)
  in  s
  end
and compsubstRoot theta =
  let fun s (COMPVAL t) = COMPVAL (tysubstRoot theta t)
        | s (COMPABSTY path) = COMPABSTY (pathsubstRoot theta path)
        | s (COMPMANTY t)  = COMPMANTY (tysubstRoot theta t)
        | s (COMPMOD mt)  = COMPMOD (mtsubstRoot theta mt)
  in  s
  end
(* <boxed values 167>=                          *)
val _ = op mtsubstRoot   : rootsubst -> modty      -> modty
val _ = op compsubstRoot : rootsubst -> component -> component
(* <substitutions for \mcl>=                    *)
fun tysubstManifest mantypes =
  let fun r (TYNAME path) = getOpt (associatedWith (path, mantypes), TYNAME path
                                                                               )
        | r (FUNTY (args, res)) = FUNTY (map r args, r res)
        | r (ANYTYPE) = ANYTYPE
  in  r
  end
(* <boxed values 168>=                          *)
val _ = op tysubstManifest : tysubst -> ty -> ty
(* <substitutions for \mcl>=                    *)
fun mtsubstManifest mantypes mt =
  let val newty = tysubstManifest mantypes
      fun newmt (MTEXPORTS cs) = MTEXPORTS (map (fn (x, c) => (x, newcomp c)) cs
                                                                               )
        | newmt (MTALLOF mts)  = MTALLOF (map newmt mts)
                                             (* can't violate unmix invariant *)
        | newmt (MTARROW (args, result)) =
            MTARROW (map (fn (x, mt) => (x, newmt mt)) args, newmt result)
      and newcomp (COMPVAL tau) = COMPVAL (newty tau)
        | newcomp (COMPABSTY p) =
           (case associatedWith (p, mantypes)
              of SOME tau => COMPMANTY tau
               | NONE => COMPABSTY p)   (* used to be this on every path *)
        | newcomp (COMPMANTY tau) = COMPMANTY (newty tau)
        | newcomp (COMPMOD mt) = COMPMOD (newmt mt)
  in  newmt mt
  end
(* <boxed values 169>=                          *)
val _ = op mtsubstManifest : tysubst -> modty -> modty
(* <type components of module types>=           *)
fun abstractTypePaths (MTEXPORTS cs, path : path) =
      let fun mts (t, COMPABSTY _) = [PDOT (path, t)]
            | mts (x, COMPMOD mt) = abstractTypePaths (mt, PDOT (path, x))
            | mts _ = []
(* An invariant on combined module types        *)
(*                                              *)
(* Important invariant of the least upper bound: In any *)
(* semantic [[MTALLOF]], if a type name appears as *)
(* manifest in any alternative, it appears only as *)
(* manifest, never as abstract—and the module type has *)
(* no references to an abstract type of that name. *)
(*                                              *)
(* Violations of this invariant are detected by function *)
(* [[mixedManifestations]].                     *)
(* <boxed values 130>=                          *)
val _ = op abstractTypePaths : modty rooted -> path list
      in  (List.concat o map mts) cs
      end
  | abstractTypePaths (MTALLOF mts, path) =
      (List.concat o map (fn mt => abstractTypePaths (mt, path))) mts
  | abstractTypePaths (MTARROW _, _) = []
                                          (* could be bogus, cf Leroy rule 21 *)
(* Realization                                  *)
(*                                              *)
(* This general-purpose code ought to go elsewhere. *)
(* <utilities for module-type realization>=     *)
fun filterdec p (MTARROW f, path) = MTARROW f
  | filterdec p (MTALLOF mts, path) = MTALLOF (map (fn mt => filterdec p (mt,
                                                                     path)) mts)
  | filterdec p (MTEXPORTS xcs, path) =
      let fun cons ((x, c), xcs) =
            let val path = PDOT (path, x)
                val c = case c of COMPMOD mt => COMPMOD (filterdec p (mt, path))
                                | _ => c
            in  if p (c, path) then
                  (x, c) :: xcs
                else
                  xcs
            end
      in  MTEXPORTS (foldr cons [] xcs)
      end
(* <utilities for module-type realization>=     *)
fun emptyExports (MTEXPORTS []) = true
  | emptyExports _ = false

(* <module-type realization>=                   *)
fun manifestSubsn (MTEXPORTS cs, path) =
      let fun mts (x, COMPMANTY tau) = [(PDOT (path, x), tau)]
            | mts (x, COMPMOD mt) = manifestSubsn (mt, PDOT(path, x))
            | mts _ = []
      in  (List.concat o map mts) cs
      end
  | manifestSubsn (MTALLOF mts, path) =
      (List.concat o map (fn mt => manifestSubsn (mt, path))) mts
  | manifestSubsn (MTARROW _, path) = []
                                          (* could be bogus, cf Leroy rule 21 *)
(* NOT CLEAR IF THIS BELONGS HERE OR IN SUPPLEMENT. *)
(* <boxed values 133>=                          *)
val _ = op manifestSubsn : modty rooted -> tysubst
(* This is purely a heuristic to get things looking *)
(* nice. We filter out redundant manifest-type  *)
(* declarations, and we drop any argument that consists *)
(* only of redundant declarations (or is otherwise *)
(* empty).                                      *)
(* <module-type realization>=                   *)
val simpleSyntacticMeet : modty -> modty =
  let val path = PNAME (MODTYPLACEHOLDER "syntactic meet")
      fun filterManifest (prev', []) = rev prev'
        | filterManifest (prev', mt :: mts) =
            let val manifests = manifestSubsn (MTALLOF prev', path)
                fun redundant (COMPMANTY tau, p) =
                      (case associatedWith (p, manifests)
                         of SOME tau' => eqType (tau, tau')
                          | NONE => false)
                  | redundant _ = false
            in  filterManifest (filterdec (not o redundant) (mt, path) :: prev',
                                                                            mts)
            end
      val filterManifest = fn mts => filterManifest ([], mts)
      fun mtall [mt] = mt
        | mtall mts  = MTALLOF mts
      val meet = mtall o List.filter (not o emptyExports) o filterManifest
  in  fn (MTALLOF mts) => meet mts
       | mt => mt
  end
(* It establishes this invariant: In any semantic *)
(* [[MTALLOF]], if a type name appears as manifest in *)
(* any alternative, it appears only as manifest, never *)
(* as abstract—and the module type has no references to *)
(* an abstract type of that name.               *)
(* <module-type realization>=                   *)
fun allofAt (mts, path) =  (* smart constructor, rooted module type *)
  let val mt = MTALLOF mts
      val mantypes = manifestSubsn (mt, path)
      val abstypes = abstractTypePaths (mt, path)
  in  if List.exists (hasKey mantypes) abstypes then
        simpleSyntacticMeet (mtsubstManifest mantypes mt)
      else
        mt
  end
(* <module-type realization>=                   *)
fun unmixTypes (mt, path) =
  let fun mtype (MTEXPORTS cs) = MTEXPORTS (map comp cs)
        | mtype (MTALLOF mts)  = allofAt (map mtype mts, path)
        | mtype (MTARROW (args, result)) =
            MTARROW (map (fn (x, mt) => (x, mtype mt)) args, mtype result)
      and comp (x, COMPMOD mt) = (x, COMPMOD (unmixTypes (mt, PDOT (path, x))))
        | comp c = c
  in  mtype mt
  end
(* Restores the invariant at need.              *)
(* <boxed values 170>=                          *)
val _ = op unmixTypes : modty rooted -> modty
(* <invariants of \mcl>=                        *)
fun mixedManifestations mt =
  let val path = PNAME (MODTYPLACEHOLDER "invariant checking")
      val manifests = manifestSubsn (mt, path)
      val abstracts = abstractTypePaths (mt, path)
  in  List.exists (hasKey manifests) abstracts
  end
(* <[[implements]] relation, based on [[subtype]] of two module types>= *)
infix 1 >>
fun (OK ()) >> c = c
  | (ERROR msg) >> _ = ERROR msg

fun allE []      = OK ()
  | allE (e::es) = e >> allE es

fun subtype mts =
  let fun st (MTARROW (args, res), MTARROW (args', res')) =
            unimp "subtyping on arrow modules -- need to make reflexive"
        | st (MTARROW (args, _), _) =
            ERROR ("expected an exporting module but got one that takes " ^
                   countString args "parameter")
        | st (_, MTARROW (args, _)) =
            ERROR ("expected a module that takes " ^
                   countString args "parameter" ^
                                                ", but got an exporting module")
        | st (mt, MTALLOF mts') =
            allE (map (fn mt' => st (mt, mt')) mts')
        | st (mt, MTEXPORTS comps') =
            compsSubtype (components mt, comps')
      and components (MTEXPORTS cs) = cs
        | components (MTALLOF mts) = List.concat (map components mts)
        | components (MTARROW _) = raise InternalError "meet of arrow types"
      and compsSubtype (comps, comps') =
            let fun supplied (x, _) = List.exists (fn (y, _) => x = y) comps
                val (present, absent) = List.partition supplied comps'
                fun check (x, supercomp) =
                  let (* <definition of [[csubtype]]>=                *)
                      fun csubtype (COMPVAL tau, COMPVAL tau') =
                            if eqType (tau, tau') then OK ()
                            else ERROR ("interface calls for value " ^ x ^
                                                              " to have type " ^
                                        typeString tau' ^ ", but it has type " ^
                                                                 typeString tau)
                        | csubtype (COMPABSTY _, COMPABSTY _) = OK ()
                                   (* XXX really OK? without comparing paths? *)
                        | csubtype (COMPMANTY _, COMPABSTY _) = OK ()
                                                             (* XXX likewise? *)
                        | csubtype (COMPMANTY tau, COMPMANTY tau') = 
                            if eqType (tau, tau') then OK ()
                            else ERROR ("interface calls for type " ^ x ^
                                                       " to manifestly equal " ^
                                        typeString tau' ^ ", but it is " ^
                                                                 typeString tau)
                        | csubtype (COMPABSTY path, COMPMANTY tau') =
                            if eqType (TYNAME path, tau') then OK ()
                            else ERROR ("interface calls for type " ^ x ^
                                                       " to manifestly equal " ^
                                        typeString tau' ^ ", but it is " ^
                                                       typeString (TYNAME path))
                        | csubtype (COMPMOD m, COMPMOD m') =
                            subtype (m, m')
                        | csubtype (c, c') =
                            ERROR ("interface calls for " ^ x ^ " to be " ^
                                                                   whatcomp c' ^
                                   ", but implementation provides " ^ whatcomp c
                                                                               )
                      (* THIS ONE LOOKS GOOD AND IMPORTANT            *)
                      (* <boxed values 132>=                          *)
                      val _ = op csubtype : component * component -> unit error
(* Module subtyping                             *)
(*                                              *)
(* MUST UNDERSTAND LEROY'S SUBSTITUTIONS HERE.  *)
(*                                              *)
(* IDEAS:                                       *)
(*                                              *)
(*   • Witness to lack of subtype should be keyed by *)
(*  path.                                       *)
(*   • Error message should tell the whole story, e.g., *)
(*  ``context requires that [[t]] be both [[int]] and *)
(*  [[bool]].''                                 *)
(*   • Try a cheap and cheerful solution to uninhabited *)
(*  intersections, e.g., incompatible manifest types? *)
(*                                              *)
(* <boxed values 131>=                          *)
val _ = op csubtype : component * component -> unit error
val _ = op subtype  : modty * modty -> unit error
                  in  csubtype (find (x, comps), supercomp)
                  end
                    handle NotFound y => raise InternalError
                                                      "missed present component"
                val missedMsg =
                  if null absent then OK ()
                  else
                    ERROR (
                    "an interface expected some components that are missing: " ^
                           commaSep
                           (map (fn (x, c) => x ^ " (" ^ whatcomp c ^ ")")
                                                                        absent))
            in  allE (map check present) >> missedMsg
            end
  in  st mts
  end
(* KEY THING! This is my approximation of Leroy's *)
(* [[modtype_match]]. Instead of placing type equalities *)
(* in an environment, I substitute. The ice is getting *)
(* thin here.                                   *)
(* <[[implements]] relation, based on [[subtype]] of two module types>= *)
val mtsubstManifestDebug = fn theta => fn (super, p) =>
  let val mt' = mtsubstManifest theta super
      val () = app eprint [countString theta "substitution", "\n"]
      val () = app (fn (pi, tau) => app eprint ["   ", pathString pi, " |--> ",
                                                    typeString tau, "\n"]) theta
      val () = app eprint ["realized: ", mtString mt', "\n"]
      
  in  mt'
  end
fun implements (p : path, submt, supermt) =
 (*   (app eprint ["At ", pathString p,
                   "\n  sub:  ", mtString submt, "\n  sup: ", mtString supermt,
                                                                      "\n"]; id)
  *)
  let val theta = manifestSubsn (submt, p)
  in  subtype (submt, mtsubstManifest theta supermt)  (* XXX need unmixTypes? *)
  end
(* <path-expression lookup>=                    *)
fun asBinding (COMPVAL tau, root) = ENVVAL tau
  | asBinding (COMPABSTY path, root) = ENVMANTY (TYNAME path)
  | asBinding (COMPMANTY tau, root) = ENVMANTY tau
  | asBinding (COMPMOD mt, root) = ENVMOD (mt, root)

fun uproot (ENVVAL tau) = COMPVAL tau
  | uproot (ENVMANTY tau) = COMPMANTY tau
  | uproot (ENVMOD (mt, _)) = COMPMOD mt
  | uproot d = raise InternalError (whatdec d ^ " as component")

fun notModule (dcl, px) =
  raise TypeError ("looking for a module, but " ^ pathexString px ^
                   " is a " ^ whatdec dcl)
fun pathfind (PNAME x, Gamma) = find (snd x, Gamma)
  | pathfind (PDOT (path, x), Gamma) =
      let (* <definition of [[mtfind]]>=                  *)
          fun mtfind (x, mt as MTEXPORTS comps) : component option =
                 (SOME (find (x, comps)) handle NotFound _ => NONE)
            | mtfind (x, MTARROW _) =
                 raise TypeError ("tried to select component " ^ x ^
                                  " from generic module " ^ pathexString path)
            | mtfind (x, mt as MTALLOF mts) =
                (case List.mapPartial (fn mt => mtfind (x, mt)) mts
                   of [comp] => SOME comp
                    | [] => NONE
                    | _ :: _ :: _ => unimp "component in multiple signatures")
          fun noComponent (path, x, mt) =
            raise TypeError ("module " ^ pathexString path ^
                                                 " does not have a component " ^
                             pathexString (PDOT (path, x)) ^ "; its type is " ^
                                                                    mtString mt)
          (* <boxed values 135>=                          *)
          val _ = op mtfind : name * modty -> component option
      in  case pathfind (path, Gamma)
            of ENVMOD (mt, root) =>
                 (asBinding (valOf (mtfind (x, mt)), root) handle Option =>
                   noComponent (path, x, mt))
             | dec =>
               (* <tried to select [[path]].[[x]] but [[path]] is a [[dec]]>= *)
                      raise TypeError ("Tried to select " ^ pathexString (PDOT (
                                                          path, x)) ^ ", but " ^
                                       pathexString path ^ " is " ^ whatdec dec
                                                         ^ ", which does not " ^
                                       " have components")
      end
  | pathfind (PAPPLY (fpx, actualpxs) : pathex, Gamma) =
     (* This is Leroy's [[Apply]] rule. The idea is  *)
     (* summarized as follows: {mathpar} f : PiA:T.B *)
     (*                                              *)
     (* f @@ M : B[A |->M] {mathpar} This works even if B is *)
     (* itself an arrow type. Uncurrying, it means that when *)
     (* substituting for the first formal parameter, *)
     (* we substitute in all the remaining formal parameters. *)
     (* <instantiation of module [[fpx]] to [[actualpxs]]>= *)
     let fun rootedModtype px = case pathfind (px, Gamma)
                                  of ENVMOD (mt, root) => (mt, root)
                                   | dec => notModule (dec, px)
         val (fmod, actuals) = (rootedModtype fpx, map rootedModtype actualpxs)
         val (formals, result) = case fmod
                                   of (MTARROW fr, _) => fr
                                    | _ =>
                              (* Instantiation                                *)

                              (*                                              *)

                              (* <instantiated exporting module [[fpx]]>=     *)
                                           raise TypeError ("module " ^
                       pathexString fpx ^ " is an exporting module, and only " ^

                                        " a generic module can be instantiated")
         fun resty ([],                               [],
                                                                result) = result
           | resty ((formalid, formalmt) :: formals, (actmt, actroot) :: actuals
                                                                     , result) =
               let val theta = formalid |--> actroot
                   fun fsubst (ident, mt) = (ident, mtsubstRoot theta mt)
                   val mtheta = manifestSubsn (actmt, actroot)
                   val () = if true orelse null mtheta then ()
                     else app (fn (pi, tau) => app eprint ["manifestly ",
                          pathString pi, " |--> ", typeString tau, "\n"]) mtheta
                   val subst = mtsubstManifest mtheta o mtsubstRoot theta
                   (* XXX need to substitute manifest types from the actuals? *)
               in  case implements (actroot, actmt, mtsubstRoot theta formalmt)
                     of OK () => resty (map fsubst formals, actuals, subst
                                                                         result)
                      | ERROR msg =>
                      (* <can't pass [[actroot]] as [[formalid]] to [[fpx]]>= *)
                                     raise TypeError ("module " ^ pathString
                                      actroot ^ " cannot be used as argument " ^
                                                      modidentString formalid ^
                                      " to generic module " ^ pathexString fpx ^
                                                      ": " ^ msg)
               end
           | resty _ = (* <wrong number of arguments to [[fpx]]>=      *)
                       raise TypeError ("generic module " ^ pathexString fpx ^
                                                              " is expecting " ^
                                        countString formals "parameter" ^
                                                                  ", but got " ^
                                        countString actuals "actual parameter")
     in  ENVMOD (resty (formals, actuals, result), PAPPLY (root fmod, map root
                                                                       actuals))
     end
(* Looking up path expressions                  *)
(*                                              *)
(* <boxed values 134>=                          *)
val _ = op pathfind   : pathex * binding env -> binding
val _ = op asBinding : component * path -> binding
val _ = op uproot : binding -> component

fun addloc loc (PNAME x) = PNAME (loc, x)
  | addloc loc (PDOT (path, x)) = PDOT (addloc loc path, x)
  | addloc loc (PAPPLY _) = raise InternalError "application vcon"

fun vconfind (k, Gamma) = pathfind (addloc ("bogus", ~99) k, Gamma)
(* <translation of {\mcl} type syntax into types>= *)
fun txpath (px, Gamma) =
  let fun tx (PAPPLY (f, args)) = PAPPLY (tx f, map tx args)
        | tx (PDOT (p, x)) = PDOT (tx p, x)
        | tx (PNAME (loc, m)) =
            let fun bad aThing =
                  raise TypeError ("I was expecting " ^ m ^
                                                     " to refer to a module, " ^
                                   "but at " ^ srclocString loc ^ ", it's " ^
                                                                         aThing)
            in  case find (m, Gamma)
                  of ENVMODTY _ => bad "a module type"
                   | ENVMOD (mt, p) => p
                   | c => bad (whatdec c)
            end
  in  tx px
  end
val elabpath = txpath
(* Translation/elaboration of syntax into types *)
(*                                              *)
(* We translate paths, types, declarations, and module *)
(* types.                                       *)
(* <boxed values 171>=                          *)
val _ = op txpath : pathex * binding env -> path
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <translation of {\mcl} type syntax into types>= *)
fun elabty (t, Gamma) =
  let fun tx (TYNAME px) =
            (case pathfind (px, Gamma)
               of ENVMANTY tau => tau
                | dec => raise TypeError ("I was expecting a type, but " ^
                                           pathexString px ^ " is " ^ whatdec
                                                                           dec))
        | tx (FUNTY (args, res)) = FUNTY (map tx args, tx res)
        | tx ANYTYPE = ANYTYPE
  in  tx t
  end
(* <boxed values 172>=                          *)
val _ = op elabty : tyex * binding env -> ty
(* <translation of {\mcl} type syntax into types>= *)
fun findModty (x, Gamma) =
  case find (x, Gamma)
    of ENVMODTY mt => mt
     | dec => raise TypeError ("Tried to use " ^ whatdec dec ^ " " ^ x ^
                                " as a module type")
(* <boxed values 173>=                          *)
val _ = op findModty : name * binding env -> modty
(* <translation of {\mcl} type syntax into types>= *)
fun elabmt ((mtx : modtyx, path), Gamma) =
  let val resultName = PNAME (MODTYPLACEHOLDER "functor result")
      fun tx (MTNAMEDX t) = mtsubstRoot (MODTYPLACEHOLDER t |--> path) (
                                                           findModty (t, Gamma))
        | tx (MTEXPORTSX exports) =
             let val (this', _) = foldl (leftLocated export) ([], Gamma) exports
             in  MTEXPORTS (rev this')
             end
        | tx (MTALLOFX mts) = allofAt (map (located tx) mts, path)
        | tx (MTARROWX (args, body)) =
            let fun txArrow ([], (loc, body), Gamma : binding env) =
                      ([], atLoc loc elabmt ((body, resultName), Gamma))
                  | txArrow (((mloc, m), (mtloc, mtx)) :: rest, body, Gamma) =
                      let val modid = genmodident m
                          val modty = atLoc mtloc elabmt ((mtx, PNAME modid),
                                                                          Gamma)
                          val () =
                             (* <if [[modty]] is generic, bleat about [[m]]>= *)
                                   case modty
                                     of MTARROW _ =>
                                       raise TypeError ("module parameter " ^ m
                                               ^ " is generic, but a generic " ^

                    "module may not take another generic module as a parameter")
                                      | _ => ()
                          val Gamma' = bind (m, ENVMOD (modty, PNAME modid),
                                                                          Gamma)
                             (* XXX check 1st arg to ENVMOD *)
                          val (rest', body') = txArrow (rest, body, Gamma')
                      in  ((modid, modty) :: rest', body')
                      end
            in  MTARROW (txArrow (args, body, Gamma))
            end

      and export ((x, ctx : decl), (theseDecls, Gamma)) =
            if isbound (x, theseDecls) then
              raise TypeError ("duplicate declaration of " ^ x ^
                                                              " in module type")
            else
              let val c = txComp ((ctx, PDOT (path, x)), Gamma)
              in  ((x, c) :: theseDecls, bind (x, asBinding (c, path), Gamma))
              end
(* <boxed values 174>=                          *)
val _ = op elabmt : modtyx rooted * binding env -> modty
  in  tx mtx
  end
(* <translation of {\mcl} type syntax into types>= *)
and txComp ((comp : decl, path), Gamma : binding env) : component =
  let fun ty t = elabty (t, Gamma)
(* <boxed values 175>=                          *)
val _ = op txDecl    : decl rooted * binding env -> binding
val _ = op txComp    : decl rooted * binding env -> component
  in  case comp
        of DECVAL tau  => COMPVAL (ty tau)
         | DECABSTY    => COMPABSTY path
         | DECMANTY t  => COMPMANTY (ty t)
         | DECMOD mt   => COMPMOD (elabmt ((mt, path), Gamma))
                              (* XXX is path really OK here??? *)
         | DECMODTY mt =>
             raise TypeError ("module type " ^ pathString path ^
                                    " may not be a component of another module")
  end
and txDecl ((comp : decl, path), Gamma : binding env) : binding =
  let fun ty t = elabty (t, Gamma)
  in  case comp
        of DECVAL tau  => ENVVAL (ty tau)
         | DECABSTY    => ENVMANTY (TYNAME path)
         | DECMANTY t  => ENVMANTY (ty t)
         | DECMOD mt   => ENVMOD (elabmt ((mt, path), Gamma), path)
                              (* XXX is path really OK here??? *)
         | DECMODTY mt => ENVMODTY (elabmt ((mt, path), Gamma))
  end
val elabmt = fn a =>
  let val mt = elabmt a
  in  if mixedManifestations mt then
        raise BugInTypeChecking ("invariant violation (mixed M): " ^ mtString mt
                                                                               )
      else
        mt
  end
(* The initial basis                            *)
(*                                              *)
(* <primitive modules and types used to type literal expressions>= *)
val arraymodname = "Array"

val intmodident = genmodident "Int"
val symmodident = genmodident "Sym"
val boolmodident = genmodident "Bool"
val unitmodident = genmodident "Unit"
val arraymodident = genmodident arraymodname
val uarraymodident = genmodident "UnsafeArray"

val inttype = TYNAME (PDOT (PNAME intmodident, "t"))
val symtype = TYNAME (PDOT (PNAME symmodident, "t"))
val booltype = TYNAME (PDOT (PNAME boolmodident, "t"))
val unittype = TYNAME (PDOT (PNAME unitmodident, "t"))

fun arraytype tau =
  case tau
    of TYNAME (PDOT (module, "t")) =>
         TYNAME (PDOT (PAPPLY (PNAME arraymodident, [module]), "t"))
     | _ => raise InternalError "unable to form internal array type"


fun addValWith f ((x, v, ty), rho) = bind (x, f v, rho)
fun decval (x, v, ty) = (x, ENVVAL ty)
fun compval (x, v, ty) = (x, COMPVAL ty)


(* <shared utility functions for building primitives in languages with type checking>= *)
fun binaryOp f = (fn [a, b] => f (a, b) | _ => raise BugInTypeChecking "arity 2"
                                                                               )
fun unaryOp  f = (fn [a]    => f a      | _ => raise BugInTypeChecking "arity 1"
                                                                               )
(* Here are the primitives. As in Chapter [->], all are *)
(* either binary or unary operators. Type checking *)
(* should guarantee that operators are used with the *)
(* correct arity.                               *)
(* <boxed values 296>=                          *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
(* <shared utility functions for building primitives in languages with type checking>= *)
fun arithOp f =
      binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                 | _ => raise BugInTypeChecking "arithmetic on non-numbers")
(* Arithmetic primitives expect and return integers. *)
(* <boxed values 297>=                          *)
val _ = op arithOp   : (int * int -> int) -> (value list -> value)
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <primitives ((mcl))>=                        *)
fun eqPrintPrims tau strip =
  let val comptype = FUNTY ([tau, tau], booltype)
      fun comparison f = binaryOp (embedBool o (fn (x, y) => f (strip x, strip y
                                                                             )))
  in  ("similar?",  comparison op =,  comptype) ::
      ("dissimilar?",  comparison op =,  comptype) ::
      ("=",  comparison op =,  comptype) ::
      ("!=", comparison op <>, comptype) ::
      ("print", unaryOp (fn x => (print (valueString x);unitVal)), FUNTY ([tau],
                                                                   unittype)) ::
      ("println", unaryOp (fn x => (println (valueString x);unitVal)), FUNTY ([
                                                             tau], unittype)) ::
      []
  end

val symPrims =
  eqPrintPrims symtype (fn SYM s => s | _ => raise BugInTypeChecking
                                                        "comparing non-symbols")

val boolPrims =
  eqPrintPrims booltype (fn CONVAL (K, []) => K
                          | _ => raise BugInTypeChecking
                                                       "comparing non-Booleans")

(* <primitives ((mcl))>=                        *)
fun comparison f = binaryOp (embedBool o f)
fun intcompare f = 
      comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                   | _ => raise BugInTypeChecking "comparing non-numbers")

fun asInt (NUM n) = n
  | asInt v = raise BugInTypeChecking ("expected a number; got " ^ valueString v
                                                                               )

val arithtype = FUNTY ([inttype, inttype], inttype)
val comptype  = FUNTY ([inttype, inttype], booltype)

fun wordOp f = arithOp (fn (n, m) => Word.toInt (f (Word.fromInt n, Word.fromInt
                                                                            m)))
fun unaryIntOp f = unaryOp (NUM o f o asInt)
fun unaryWordOp f = unaryIntOp (Word.toInt o f o Word.fromInt)


val intPrims = 
  ("+", arithOp op +,   arithtype) :: 
  ("-", arithOp op -,   arithtype) :: 
  ("*", arithOp op *,   arithtype) :: 
  ("/", arithOp op div, arithtype) ::

  ("land", wordOp Word.andb, arithtype) ::
  ("lor", wordOp Word.orb, arithtype) ::
  (">>u", wordOp Word.>>, arithtype) ::
  (">>s", wordOp Word.~>>, arithtype) ::
  ("<<",  wordOp Word.<<, arithtype) ::

  ("of-int", unaryOp id,             FUNTY ([inttype], inttype)) ::
  ("negated", unaryIntOp ~,          FUNTY ([inttype], inttype)) ::
  ("lnot", unaryWordOp Word.notb, FUNTY ([inttype], inttype)) ::

  ("<",  intcompare op <,  comptype) :: 
  (">",  intcompare op >,  comptype) ::
  ("<=", intcompare op <=, comptype) :: 
  (">=", intcompare op >=, comptype) ::
  ("printu", unaryOp (fn n => (printUTF8 (asInt n); unitVal)), FUNTY ([inttype],
                                                                   unittype)) ::
  eqPrintPrims inttype (fn NUM n => n | _ => raise BugInTypeChecking
                                                        "comparing non-numbers")
(* <primitives ((mcl))>=                        *)
local
  val arraypath = PNAME arraymodident
  val arrayarg  = genmodident "Elem"
  val argpath   = PNAME arrayarg
  val resultpath = PAPPLY (arraypath, [argpath])
  val elemtype   = TYNAME (PDOT (argpath, "t"))
  val arraytype  = TYNAME (PDOT (resultpath, "t"))


  fun protect f x = f x
    handle Size      => raise RuntimeError "array too big"
         | Subscript => raise RuntimeError "array index out of bounds"


  fun asArray (ARRAY a) = a
    | asArray _         = raise BugInTypeChecking "non-array value as array"
  fun arrayLeft f (a, x) = f (asArray a, x)
in
  val arrayPrims = 
    ("size", unaryOp (NUM o Array.length o asArray), FUNTY ([arraytype], inttype
                                                                           )) ::
    ("new", binaryOp (fn (NUM n, a) => ARRAY (protect Array.array (n, a))
                       | _ => raise BugInTypeChecking "array size not a number")
                                                                               ,
            FUNTY ([inttype, elemtype], arraytype)) ::
    ("empty", fn _ => ARRAY (Array.fromList []), FUNTY ([], arraytype)) ::
    ("at", binaryOp (fn (ARRAY a, NUM i) => protect Array.sub (a, i)
                      | _ => raise BugInTypeChecking "Array.at array or index"),
            FUNTY ([arraytype, inttype], elemtype)) ::
    ("at-put", fn [ARRAY a, NUM i, x] => (protect Array.update (a, i, x);
                                                                        unitVal)
                | _ => raise BugInTypeChecking
                                      "number or types of args to Array.at-put",
            FUNTY ([arraytype, inttype, elemtype], unittype)) ::
    []

  val arraymodtype : modty =
    MTARROW ([(arrayarg, MTEXPORTS [("t", COMPABSTY (PDOT (argpath, "t")))]  :
                                                                        modty)],
             MTEXPORTS (("t", COMPABSTY (PDOT (resultpath, "t"))) ::
                        ("elem", COMPMANTY elemtype) ::
                        map compval arrayPrims) : modty)

  val uarrayPrims = 
    ("new", unaryOp (fn (NUM n) => ARRAY (protect Array.array (n, CONVAL (PNAME
                                                          "uninitialized", [])))
                       | _ => raise BugInTypeChecking "array size not a number")
                                                                               ,
            FUNTY ([inttype], arraytype)) ::
    []

  val uarraymodtype : modty =
    MTARROW ([(arrayarg, MTEXPORTS [("t", COMPABSTY (PDOT (argpath, "t")))]  :
                                                                        modty)],
             MTEXPORTS (("t", COMPABSTY (PDOT (resultpath, "t"))) ::
                        map compval uarrayPrims) : modty)
end
(* <primitives ((mcl))>=                        *)
fun inject_bool x =
      CONVAL (PNAME (if x then "#t" else "#f"), [])
fun project_bool (CONVAL (PNAME "#t", [])) = true
  | project_bool (CONVAL (PNAME "#f", [])) = false
  | project_bool _ = raise RuntimeError "projected non-boolean"

fun inject_predicate f = fn x => inject_bool (f x)
fun predop f = unaryOp (inject_predicate f)

fun comparison f = binaryOp (inject_predicate f)
fun intcompare f = comparison (
                     fn (NUM n1, NUM n2) => f (n1, n2)
                      | _ => raise BugInTypeChecking "integers expected")
(* <boxed values 196>=                          *)
val _ = op inject_bool  : bool -> value
val _ = op project_bool : value -> bool
(* And here come the predicates. Equality comparison *)
(* succeeds only on symbols and numbers. The empty list *)
(* is dealt with through [[case]] expressions.  *)


val unitval = 
  ("unit", CONVAL (PNAME "unit", []), TYNAME (PDOT (PNAME unitmodident, "t")))

local
  fun module id primvals : binding =
    ENVMOD (MTEXPORTS (("t", COMPABSTY (PDOT (PNAME id, "t"))) :: map compval
                                                                      primvals),
            PNAME id)
in
  val intmod  = module intmodident intPrims
  val symmod  = module symmodident symPrims
  val boolmod = module boolmodident boolPrims
  val unitmod = module unitmodident [unitval]
  val arraymod  = ENVMOD (arraymodtype, PNAME arraymodident)
  val uarraymod  = ENVMOD (uarraymodtype, PNAME uarraymodident)
end

(* Type checking for expressions                *)
(*                                              *)
(* Here's how operator overloading works:       *)
(*                                              *)
(*   • An overloaded name is associated with a sequence *)
(*  of values: one for each type at which the name is *)
(*  overloaded.                                 *)
(*   • At run time, the sequence is represented by an *)
(*  array of values.                            *)
(*   • At compile time, the sequence is represented by a *)
(*  list of types.                              *)
(*   • Adding an overloading means consing on to the *)
(*  front of the sequence.                      *)
(*   • Using an overloaded name requires an index into *)
(*  the sequence. The first matching type wins. *)
(*   • An overloaded name can be used only in a function *)
(*  application. At every application, therefore, the *)
(*  type checker writes the sequence index into the *)
(*  AST node.                                   *)
(*                                              *)
(* <utility functions on {\mcl} types>=         *)
fun firstArgType (x, FUNTY (tau :: _, _)) = OK tau
  | firstArgType (x, FUNTY ([], _)) =
      ERROR ("function " ^ x ^
                 " cannot be overloaded because it does not take any arguments")
  | firstArgType (x, _) =
      ERROR (x ^ " cannot be overloaded because it is not a function")

(* <utility functions on {\mcl} types>=         *)
fun okOrTypeError (OK a) = a
  | okOrTypeError (ERROR msg) = raise TypeError msg

fun ok a = okOrTypeError a handle _ => raise InternalError
                                                      "overloaded non-function?"
fun resolveOverloaded (f, argty : ty, tys : ty list) : (ty * int) error =
  let fun findAt (tau :: taus, i) = if eqType (argty, ok (firstArgType (f, tau))
                                                                          ) then
                                      OK (tau, i)
                                    else
                                      findAt (taus, i + 1)
        | findAt ([], _) =
            ERROR ("cannot figure out how to resolve overloaded name " ^ f ^
                   " when applied to first argument of type " ^ typeString argty
                                                                               ^
                   " (resolvable: " ^ separate ("", ", ") (map typeString tys) ^
                                                                            ")")
  in  findAt (tys, 0)
  end
(* <boxed values 137>=                          *)
val _ = op resolveOverloaded : name * ty * ty list -> (ty * int) error
(* <[[typeof]] a {\mcl} expression ((prototype))>= *)
fun typeof (e, Gamma) : ty = raise LeftAsExercise "typeof"
(* <principal type of a module>=                *)
fun strengthen (MTEXPORTS comps, p) =
      let fun comp (c as (x, dc)) =
            case dc
              of COMPABSTY _ => (x, COMPMANTY (TYNAME (PDOT (p, x))))
               | COMPMOD mt  => (x, COMPMOD (strengthen (mt, PDOT (p, x))))
                                                              (* XXX check me *)
               | COMPVAL   _ => c
               | COMPMANTY _ => c
      in  MTEXPORTS (map comp comps)
      end
  | strengthen (MTALLOF mts, p) =
      allofAt (map (fn mt => strengthen (mt, p)) mts, p)
  | strengthen (mt as MTARROW _, p) =
      mt
(* \typesystemmolecule                          *)
(*                                              *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(* {mathpar} \typeise tau                       *)
(*                                              *)
(* \tyrule Case \threeline \typeise tau \typeis\choice *)
(* p_i e_i tau-->tau_i, 1 <=i <=n tau_1 = ...= tau_n \ *)
(* typeis\xcase(e, \choicep_1 e_1, ..., \choicep_n e_n) *)
(* tau_1                                        *)
(*                                              *)
(* \tyrule Vcon Gamma(\avcon) = tau \typeis\avcontau *)
(* \typeis\choicep e tau-->tau'                 *)
(*                                              *)
(* \tyruleChoice \twoquad \pattypeisp Gamma' tau \typeis *)
(* [+Gamma'] e tau' \typeis\choicep e tau-->tau' *)
(* \pattypeisp Gamma' tau                       *)
(*                                              *)
(* \tyrulePatVcon \threeline \typeis\avcon\crossdotsktau *)
(* -->tau \pattypeisp_i Gamma'_i tau_i, 1 <=i <=k Gamma' *)
(* = Gamma'_1 \dunion...\dunionGamma'_k \pattypeis\ *)
(* applyvcon\cdotskp Gamma' tau                 *)
(*                                              *)
(* \tyrulePatBareVcon \typeis\avcontau \pattypeis\avcon\ *)
(* emptyenv tau                                 *)
(*                                              *)
(* \tyrulePatWildcard \pattypeis\astwildcard \emptyenv *)
(* tau                                          *)
(*                                              *)
(* \tyrulePatVar \pattypeisx {x |->tau} tau {mathpar} *)
(*                                              *)
(* Typing rules for monomorphic case expressions, *)
(* choices, and patterns [*]                    *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(*                                              *)
(* Type-checking modules: strengthening         *)
(*                                              *)
(* Is this the principal type of a module?      *)
(* <boxed values 139>=                          *)
val _ = op strengthen : modty rooted -> modty
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun elabDataDef ((T, vcons), context, Gamma) =
  let val tau    = TYNAME (contextDot (context, T))
      val Gamma' = bind (T, ENVMANTY tau, Gamma)
      fun translateVcon (K, tx) =
            (K, elabty (tx, Gamma'))
            handle TypeError msg =>
              raise TypeError ("in type of value constructor " ^ K ^ ", " ^ msg)
      val Ktaus = map translateVcon vcons
        
      fun validate (K, FUNTY (_, result)) =
            if eqType (result, tau) then
              ()
            else 
              (* <result type of [[K]] should be [[tau]] but is [[result]]>= *)
              raise TypeError ("value constructor " ^ K ^ " should return " ^
                                                                typeString tau ^
                               ", but it returns type " ^ typeString result)
        | validate (K, tau') =
            if eqType (tau', tau) then
              ()
            else 
              (* <type of [[K]] should be [[tau]] but is [[tau']]>= *)
              raise TypeError ("value constructor " ^ K ^ " should have " ^
                                                                typeString tau ^
                              ", but it has type " ^ typeString tau')
      val ()     = app validate Ktaus
      val ()     = ()(*addVcons (mu, Ktaus)*)
                                  (* supports exhaustiveness anal. *) (* OMIT *)
  in  (* thin ice here: the type component should be abstract? *)
      (T, ENVMANTY tau) :: map (fn (K, tau) => (K, ENVVAL tau)) Ktaus
  end
(* Elaborating definitions                      *)
(*                                              *)
(* <boxed values 144>=                          *)
val _ = op elabDataDef : data_def * context * binding env -> (name * binding)
                                                                            list
(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun ddString (_, COMPMANTY _) = "*"  (* paper over the thin ice *)
  | ddString (_, COMPVAL tau) = typeString tau
  | ddString _ = raise InternalError "component of algebraic data type"
(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun evalDataDef ((_, typed_vcons), rho) =
  let fun isfuntype (FUNTY _)         = true
        | isfuntype _                 = false
      fun addVcon ((K, t), rho) =
        let val v = if isfuntype t then
                      PRIMITIVE (fn vs => CONVAL (PNAME K, map ref vs))
                    else
                      CONVAL (PNAME K, [])
        in  bind (K, ref v, rho)
        end
(* N.B. Duplicates [[DATA]] case in [[defexps]] XXX. *)
(* <boxed values 145>=                          *)
val _ = op evalDataDef : data_def * value ref env -> value ref env * string list
  in  (foldl addVcon rho typed_vcons, map fst typed_vcons)
  end
(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun asComponent (x, ENVVAL tau) = SOME (x, COMPVAL tau)
  | asComponent (x, ENVMANTY tau) = SOME (x, COMPMANTY tau)
  | asComponent (m, ENVMOD (mt, _)) = SOME (m, COMPMOD mt)
  | asComponent (_, ENVOVLN _) = NONE
  | asComponent (_, ENVMODTY _) = raise InternalError "module type as component"

type basis = binding env * value ref env
fun processDataDef (dd, (Gamma, rho), interactivity) =
  let val bindings      = elabDataDef (dd, TOPLEVEL, Gamma)
      val Gamma'        = Gamma <+> bindings
      val comps         = List.mapPartial asComponent bindings
        (* could convert first component to abstract type here XXX *)
      val (rho', vcons) = evalDataDef (dd, rho)
      val tystrings = map ddString comps
      val _ = if prints interactivity then

         (* <print the new type and each of its value constructors for \mcl>= *)
                let val (T, _) = dd
                    val tau = (case find (T, Gamma')
                                 of ENVMANTY tau => tau
                                  | _ => raise Match)
                              handle _ => raise InternalError
                                                        "datatype is not a type"
                    val (kind, vcon_types) =
                      case tystrings of s :: ss => (s, ss)
                                      | [] => let exception NoKindString in
                                                          raise NoKindString end
                in  ( println (typeString tau ^ " :: " ^ kind)
                    ; ListPair.appEq (fn (K, tau) => println (K ^ " : " ^ tau))
                                                             (vcons, vcon_types)
                    )
                end
              else
                ()
  in  (Gamma', rho')
  end
(* <boxed values 146>=                          *)
val _ = op processDataDef : data_def * basis * interactivity -> basis
(* <elaborate a {\mcl} definition>=             *)
fun declarableResponse c =
      case c
        of ENVMODTY mt => mtString mt
         | ENVVAL tau => typeString tau
         | ENVMANTY _ => "manifest type"
         | ENVMOD (mt, _) => mtString mt
         | ENVOVLN _ => "overloaded name"
(* <elaborate a {\mcl} definition>=             *)
fun printStrings ss _ vs = 
  app print ss
type value_printer = (name -> ty -> value -> unit) -> value list -> unit

fun printMt what m how mt = printStrings [what, " ", m, " ", how, " ", mtString
                                                                             mt]

fun defResponse (x, c) =
  case c
    of ENVVAL tau =>
         (fn printfun => fn [v] => (printfun x tau v; app print [" : ",
                                                                typeString tau])
                          | _ => raise InternalError
                                               "value count for val definition")
     | ENVMANTY tau =>
         let val expansion = typeString tau
         in  if x = expansion then
               printStrings ["abstract type ", x]
             else
               printStrings ["type ", x, " = ", typeString tau]
         end
     | ENVMOD (mt as MTARROW _, _) => printMt "generic module" x ":" mt
     | ENVMOD (mt, _)              => printMt "module" x ":" mt
     | ENVMODTY mt                 => printMt "module type" x "=" mt
     | ENVOVLN _ => raise InternalError "defResponse to overloaded name"
(* <boxed values 141>=                          *)
val _ = op printStrings : string list -> value_printer
val _ = op defResponse : name * binding -> value_printer
(* <elaborate a {\mcl} definition>=             *)
fun defName (VAL (x, _)) = x
  | defName (VALREC (x, _, _)) = x
  | defName (EXP _) = "it"
  | defName (QNAME _) = raise InternalError "defName QNAME"
  | defName (DEFINE (x, _, _)) = x
  | defName (TYPE (t, _)) = t
  | defName (DATA (t, _)) = raise InternalError "defName DATA"
  | defName (OVERLOAD _) = raise InternalError "defName OVERLOAD"
  | defName (MODULE (m, _)) = m
  | defName (GMODULE (m, _, _)) = m
  | defName (MODULETYPE (t, _)) = t

fun defPrinter (d, Gamma) =
      let val x = defName d
      in  defResponse (x, find (x, Gamma))
          handle NotFound _ => raise InternalError "defName not found"
      end
(* <boxed values 142>=                          *)
val _ = op defPrinter : baredef * binding env -> value_printer
(* <elaborate a {\mcl} definition>=             *)
fun findModule (px, Gamma) =
  case pathfind (px, Gamma)
    of ENVMOD (mt, _) => mt
     | dec => raise TypeError ("looking for a module, but " ^ pathexString px ^
                                " is a " ^ whatdec dec)
(* <elaborate a {\mcl} definition>=             *)
(* <more overloading things>=                   *)
fun overloadBinding (p, Gamma) = 
  let val (tau, first) =
        case pathfind (p, Gamma)
          of ENVVAL tau => (tau, okOrTypeError (firstArgType (pathexString p,
                                                                          tau)))
           | c => (* <can't overload a [[c]]>=                    *)
                  raise TypeError ("only functions can be overloaded, but " ^
                                                               whatdec c ^ " " ^
                                   pathexString p ^ " is not a function")
      val x = plast p

      val currentTypes =
        (case find (x, Gamma)
           of ENVOVLN vals => vals
            | _ => []) handle NotFound _ => []
  in  (x, ENVOVLN (tau :: currentTypes))
  end

fun overloadBindings (ps, Gamma) =
  let fun add (bs', Gamma, []) = bs'
        | add (bs', Gamma, p :: ps) =
            let val b = overloadBinding (p, Gamma)
            in  add (b :: bs', Gamma <+> [b], ps)
            end
  in  add ([], Gamma, ps)
  end
fun elabd (d : baredef, context, Gamma) =
  let fun toplevel what =
        case context
          of TOPLEVEL => id
           | _ => raise TypeError (what ^ " cannot appear " ^ contextString
                                                                        context)
      (* <new definition of [[mtypeof]]>=             *)
      fun mtypeof ((m, path), Gamma) =
        let fun ty (MPATH p) = strengthen (findModule (p, Gamma), txpath (p,
                                                                         Gamma))
                                   (* YYY only use of txpath --- move it? *)
              | ty (MPATHSEALED (mtx, p)) = sealed (mtx, ty (MPATH p))
              | ty (MUNSEALED defs)       = principal defs
              | ty (MSEALED (mtx, defs))  = sealed (mtx, principal defs)
            and sealed (mtx, mt') =
                  let val mt = elabmt ((mtx, path), Gamma)
                  in  case implements (path, mt', mt)
                        of OK () => mt
                         | ERROR msg => raise TypeError msg
                  end
            and principal ds = MTEXPORTS (elabdefs (ds, INMODULE path, Gamma))
            and elabdefs ([],    c, Gamma) = [] : (name * component) list
              | elabdefs ((loc, d) :: ds, c, Gamma) =
                  let val bindings = atLoc loc elabd (d, c, Gamma)
                      val comps'   = List.mapPartial asComponent bindings
                      val Gamma'   = Gamma <+> bindings
                      val comps''  = elabdefs (ds, c, Gamma')
                      (* <definition of [[asUnique]]>=                *)
                      fun asUnique following (x, c : component) =
                        let val c' = find (x, following)
                        in  case (c, c')
                              of (COMPVAL _, COMPVAL _) => NONE
                                                    (* repeated values are OK *)
                               | _ => raise TypeError ("Redefinition of " ^
                                                          whatcomp c ^ " " ^ x ^
                                                       " in module " ^
                                                                pathString path)
                        end handle NotFound _ => SOME (x, c)        
                  in  List.mapPartial (asUnique comps'') comps' @ comps''
                  end
        in  ty m
        end
      (* <boxed values 143>=                          *)
      val _ = op elabd : baredef * context * binding env -> (name * binding)
                                                                            list
      (* <boxed values 143>=                          *)
      type value_printer = value_printer
      val _ = op mtypeof : moddef rooted * binding env -> modty
      (* WILL WANT TO ADD A CONTEXT TO IDENTIFY THE MODULE TO *)
      (* [[subtypeError]].                            *)

  in  case d
        of EXP e => toplevel ("an expression (like " ^ expString e ^ ")")
                    (elabd (VAL ("it", e), context, Gamma))
         | MODULETYPE (T, mtx) =>
             let val mt = elabmt ((mtx, PNAME (MODTYPLACEHOLDER T)), Gamma)
             in  toplevel ("a module type (like " ^ T ^ ")")
                 [(T, ENVMODTY mt)]
             end
         | MODULE (name, mx) =>
             let val root = contextDot (context, name)
                 val mt   = mtypeof ((mx, root), Gamma)
             in  [(name, ENVMOD (mt, root))]
             end
         | GMODULE (f, formals, body) =>
             let val () = toplevel ("a generic module (like " ^ f ^ ")") ()
                 val fpath     = contextDot (context, f)
                 val idformals = map (fn (x, mtx) => (genmodident x, (x, mtx)))
                                                                         formals
                 val resultpath = PAPPLY (fpath, map (PNAME o fst) idformals)

                 fun addarg arg (args, res) = (arg :: args, res)

                 fun arrowtype ((mid : modident, (x, mtx)) :: rest, Gamma) =
                       let val mt = elabmt ((mtx, PNAME mid), Gamma)
                           val Gamma' = bind (x, ENVMOD (mt, PNAME mid), Gamma)
                       in  addarg (mid, mt) (arrowtype (rest, Gamma'))
                       end
                   | arrowtype ([], Gamma) = ([], mtypeof ((body, resultpath),
                                                                         Gamma))
                 val mt = MTARROW (arrowtype (idformals, Gamma))
             in  [(f, ENVMOD (mt, fpath))]
             end       
         | QNAME px => toplevel ("a qualified name (like " ^ pathexString px ^
                                                                            ")")
                       (elabd (EXP (VAR px), context, Gamma))
         | DEFINE (name, tau, lambda as (formals, body)) =>
             let val funty = FUNTY (map (fn (n, ty) => ty) formals, tau)
             in  elabd (VALREC (name, funty, LAMBDA lambda), context, Gamma)
             end
         | VAL (x, e) =>
             let val tau = typeof (e, Gamma)
             in  [(x, ENVVAL tau)]
             end
         | VALREC (f, tau, e as LAMBDA _) =>
             let val tau    = elabty (tau, Gamma)
                 val Gamma' = bind (f, ENVVAL tau, Gamma)
                 val tau'   = typeof (e, Gamma')
             in  if not (eqType (tau, tau')) then
                   raise TypeError ("identifier " ^ f ^
                                    " is declared to have type " ^
                                    typeString tau ^ " but has actual type " ^
                                    typeString tau')
                 else
                   [(f, ENVVAL tau)]
             end
         | VALREC (name, tau, _) =>
             raise TypeError ("(val-rec [" ^ name ^ " : " ^ tyexString tau ^
                              "] ...) must use (lambda ...) on right-hand side")
         | TYPE (t, tx) =>
             let val tau = elabty (tx, Gamma)
             in  [(t, ENVMANTY tau)]
             end
         | DATA dd => elabDataDef (dd, context, Gamma)
         | OVERLOAD ovl => overloadBindings (ovl, Gamma)
  end



(*****************************************************************)
(*                                                               *)
(*   SUBSTITUTIONS FOR \MCL                                      *)
(*                                                               *)
(*****************************************************************)

(* <substitutions for \mcl>=                    *)
type rootsubst = (modident * path) list
val idsubst = []
(* <boxed values 161>=                          *)
type rootsubst = rootsubst
val _ = op idsubst : rootsubst
(* <substitutions for \mcl>=                    *)
infix 7 |-->
fun id |--> p = [(id, p)]
(* <boxed values 162>=                          *)
val _ = op |--> : modident * path -> rootsubst
(* <substitutions for \mcl>=                    *)
type tysubst = (path * ty) list
fun associatedWith (x, []) =
      NONE
  | associatedWith (x, (key, value) :: pairs) =
      if x = key then SOME value else associatedWith (x, pairs)

fun hasKey [] x = false
  | hasKey ((key, value) :: pairs) x = x = key orelse hasKey pairs x
(* <boxed values 163>=                          *)
type tysubst = tysubst
val _ = op associatedWith : path * tysubst -> ty option
val _ = op hasKey : tysubst -> path -> bool
(* <substitutions for \mcl>=                    *)
fun pathsubstRoot theta =
  let fun subst (PNAME id) =
            (case List.find (fn (id', p') => id = id') theta
               of SOME (_, p) => p
                | NONE => PNAME id)
        | subst (PDOT (p, x)) = PDOT (subst p, x)
        | subst (PAPPLY (p, ps)) = PAPPLY (subst p, map subst ps)
  in  subst
  end
(* <boxed values 164>=                          *)
val _ = op pathsubstRoot : rootsubst -> path -> path
(* <substitutions for \mcl>=                    *)
fun tysubstRoot theta (TYNAME p)          = TYNAME (pathsubstRoot theta p)
  | tysubstRoot theta (FUNTY (args, res)) =
      FUNTY (map (tysubstRoot theta) args, tysubstRoot theta res)
  | tysubstRoot theta ANYTYPE = ANYTYPE
(* <boxed values 165>=                          *)
val _ = op tysubstRoot : rootsubst -> ty -> ty
(* <substitutions for \mcl>=                    *)
fun dom theta = map (fn (a, _) => a) theta
fun compose (theta2, theta1) =
  let val domain  = union (dom theta2, dom theta1)
      val replace = pathsubstRoot theta2 o pathsubstRoot theta1 o PNAME
  in  map (fn a => (a, replace a)) domain
  end
(* <boxed values 166>=                          *)
val _ = op dom     : rootsubst -> modident set
val _ = op compose : rootsubst * rootsubst -> rootsubst
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <substitutions for \mcl>=                    *)
fun bsubstRoot s = 
  map (fn (x, a) => (x, s a))

fun mtsubstRoot theta =
  let fun s (MTEXPORTS comps)     = MTEXPORTS (bsubstRoot (compsubstRoot theta)
                                                                          comps)
        | s (MTALLOF mts)         = MTALLOF (map s mts)
        | s (MTARROW (args, res)) = MTARROW (bsubstRoot s args, s res)
  in  s
  end
and compsubstRoot theta =
  let fun s (COMPVAL t) = COMPVAL (tysubstRoot theta t)
        | s (COMPABSTY path) = COMPABSTY (pathsubstRoot theta path)
        | s (COMPMANTY t)  = COMPMANTY (tysubstRoot theta t)
        | s (COMPMOD mt)  = COMPMOD (mtsubstRoot theta mt)
  in  s
  end
(* <boxed values 167>=                          *)
val _ = op mtsubstRoot   : rootsubst -> modty      -> modty
val _ = op compsubstRoot : rootsubst -> component -> component
(* <substitutions for \mcl>=                    *)
fun tysubstManifest mantypes =
  let fun r (TYNAME path) = getOpt (associatedWith (path, mantypes), TYNAME path
                                                                               )
        | r (FUNTY (args, res)) = FUNTY (map r args, r res)
        | r (ANYTYPE) = ANYTYPE
  in  r
  end
(* <boxed values 168>=                          *)
val _ = op tysubstManifest : tysubst -> ty -> ty
(* <substitutions for \mcl>=                    *)
fun mtsubstManifest mantypes mt =
  let val newty = tysubstManifest mantypes
      fun newmt (MTEXPORTS cs) = MTEXPORTS (map (fn (x, c) => (x, newcomp c)) cs
                                                                               )
        | newmt (MTALLOF mts)  = MTALLOF (map newmt mts)
                                             (* can't violate unmix invariant *)
        | newmt (MTARROW (args, result)) =
            MTARROW (map (fn (x, mt) => (x, newmt mt)) args, newmt result)
      and newcomp (COMPVAL tau) = COMPVAL (newty tau)
        | newcomp (COMPABSTY p) =
           (case associatedWith (p, mantypes)
              of SOME tau => COMPMANTY tau
               | NONE => COMPABSTY p)   (* used to be this on every path *)
        | newcomp (COMPMANTY tau) = COMPMANTY (newty tau)
        | newcomp (COMPMOD mt) = COMPMOD (newmt mt)
  in  newmt mt
  end
(* <boxed values 169>=                          *)
val _ = op mtsubstManifest : tysubst -> modty -> modty



(*****************************************************************)
(*                                                               *)
(*   TRANSLATION OF {\MCL} TYPE SYNTAX INTO TYPES                *)
(*                                                               *)
(*****************************************************************)

(* <translation of {\mcl} type syntax into types>= *)
fun txpath (px, Gamma) =
  let fun tx (PAPPLY (f, args)) = PAPPLY (tx f, map tx args)
        | tx (PDOT (p, x)) = PDOT (tx p, x)
        | tx (PNAME (loc, m)) =
            let fun bad aThing =
                  raise TypeError ("I was expecting " ^ m ^
                                                     " to refer to a module, " ^
                                   "but at " ^ srclocString loc ^ ", it's " ^
                                                                         aThing)
            in  case find (m, Gamma)
                  of ENVMODTY _ => bad "a module type"
                   | ENVMOD (mt, p) => p
                   | c => bad (whatdec c)
            end
  in  tx px
  end
val elabpath = txpath
(* Translation/elaboration of syntax into types *)
(*                                              *)
(* We translate paths, types, declarations, and module *)
(* types.                                       *)
(* <boxed values 171>=                          *)
val _ = op txpath : pathex * binding env -> path
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <translation of {\mcl} type syntax into types>= *)
fun elabty (t, Gamma) =
  let fun tx (TYNAME px) =
            (case pathfind (px, Gamma)
               of ENVMANTY tau => tau
                | dec => raise TypeError ("I was expecting a type, but " ^
                                           pathexString px ^ " is " ^ whatdec
                                                                           dec))
        | tx (FUNTY (args, res)) = FUNTY (map tx args, tx res)
        | tx ANYTYPE = ANYTYPE
  in  tx t
  end
(* <boxed values 172>=                          *)
val _ = op elabty : tyex * binding env -> ty
(* <translation of {\mcl} type syntax into types>= *)
fun findModty (x, Gamma) =
  case find (x, Gamma)
    of ENVMODTY mt => mt
     | dec => raise TypeError ("Tried to use " ^ whatdec dec ^ " " ^ x ^
                                " as a module type")
(* <boxed values 173>=                          *)
val _ = op findModty : name * binding env -> modty
(* <translation of {\mcl} type syntax into types>= *)
fun elabmt ((mtx : modtyx, path), Gamma) =
  let val resultName = PNAME (MODTYPLACEHOLDER "functor result")
      fun tx (MTNAMEDX t) = mtsubstRoot (MODTYPLACEHOLDER t |--> path) (
                                                           findModty (t, Gamma))
        | tx (MTEXPORTSX exports) =
             let val (this', _) = foldl (leftLocated export) ([], Gamma) exports
             in  MTEXPORTS (rev this')
             end
        | tx (MTALLOFX mts) = allofAt (map (located tx) mts, path)
        | tx (MTARROWX (args, body)) =
            let fun txArrow ([], (loc, body), Gamma : binding env) =
                      ([], atLoc loc elabmt ((body, resultName), Gamma))
                  | txArrow (((mloc, m), (mtloc, mtx)) :: rest, body, Gamma) =
                      let val modid = genmodident m
                          val modty = atLoc mtloc elabmt ((mtx, PNAME modid),
                                                                          Gamma)
                          val () =
                             (* <if [[modty]] is generic, bleat about [[m]]>= *)
                                   case modty
                                     of MTARROW _ =>
                                       raise TypeError ("module parameter " ^ m
                                               ^ " is generic, but a generic " ^

                    "module may not take another generic module as a parameter")
                                      | _ => ()
                          val Gamma' = bind (m, ENVMOD (modty, PNAME modid),
                                                                          Gamma)
                             (* XXX check 1st arg to ENVMOD *)
                          val (rest', body') = txArrow (rest, body, Gamma')
                      in  ((modid, modty) :: rest', body')
                      end
            in  MTARROW (txArrow (args, body, Gamma))
            end

      and export ((x, ctx : decl), (theseDecls, Gamma)) =
            if isbound (x, theseDecls) then
              raise TypeError ("duplicate declaration of " ^ x ^
                                                              " in module type")
            else
              let val c = txComp ((ctx, PDOT (path, x)), Gamma)
              in  ((x, c) :: theseDecls, bind (x, asBinding (c, path), Gamma))
              end
(* <boxed values 174>=                          *)
val _ = op elabmt : modtyx rooted * binding env -> modty
  in  tx mtx
  end
(* <translation of {\mcl} type syntax into types>= *)
and txComp ((comp : decl, path), Gamma : binding env) : component =
  let fun ty t = elabty (t, Gamma)
(* <boxed values 175>=                          *)
val _ = op txDecl    : decl rooted * binding env -> binding
val _ = op txComp    : decl rooted * binding env -> component
  in  case comp
        of DECVAL tau  => COMPVAL (ty tau)
         | DECABSTY    => COMPABSTY path
         | DECMANTY t  => COMPMANTY (ty t)
         | DECMOD mt   => COMPMOD (elabmt ((mt, path), Gamma))
                              (* XXX is path really OK here??? *)
         | DECMODTY mt =>
             raise TypeError ("module type " ^ pathString path ^
                                    " may not be a component of another module")
  end
and txDecl ((comp : decl, path), Gamma : binding env) : binding =
  let fun ty t = elabty (t, Gamma)
  in  case comp
        of DECVAL tau  => ENVVAL (ty tau)
         | DECABSTY    => ENVMANTY (TYNAME path)
         | DECMANTY t  => ENVMANTY (ty t)
         | DECMOD mt   => ENVMOD (elabmt ((mt, path), Gamma), path)
                              (* XXX is path really OK here??? *)
         | DECMODTY mt => ENVMODTY (elabmt ((mt, path), Gamma))
  end
val elabmt = fn a =>
  let val mt = elabmt a
  in  if mixedManifestations mt then
        raise BugInTypeChecking ("invariant violation (mixed M): " ^ mtString mt
                                                                               )
      else
        mt
  end


(*****************************************************************)
(*                                                               *)
(*   TYPE CHECKING FOR {\MCL}                                    *)
(*                                                               *)
(*****************************************************************)

(* Wrapup                                       *)
(*                                              *)
(* <type checking for {\mcl}>=                  *)
(* <[[context]] for a {\mcl} definition>=       *)
datatype context
  = TOPLEVEL
  | INMODULE of path

fun contextDot (TOPLEVEL, name) = PNAME (genmodident name)
                                                     (* XXX key to uniqueness *)
  | contextDot (INMODULE path, name) = PDOT (path, name)

fun contextString TOPLEVEL = "at top level"
  | contextString (INMODULE p) = "in module " ^ pathString p
(* Type-checking modules: generativity of top-level *)
(* definitions                                  *)
(*                                              *)
(* Function [[binding]] can be used only in a known *)
(* context—because if the [[def]] defines a module, *)
(* we need to know the path for every component. *)
(* <boxed values 140>=                          *)
type context = context
val _ = op contextDot : context * name -> path
(* <type equality for \mcl>=                    *)
fun eqType (TYNAME p, TYNAME p') = p = p'
  | eqType (FUNTY (args, res), FUNTY (args', res')) =
      eqTypes (args, args') andalso eqType (res, res')
  | eqType (ANYTYPE, _) = true
  | eqType (_, ANYTYPE) = true
  | eqType _ = false
and eqTypes (taus, tau's) = ListPair.allEq eqType (taus, tau's)
(* A literal is either a bare symbol like x, which is *)
(* satisfied by [[#t]], or it is a two-element list like *)
(* \monobox(not x), which is satisfied by [[#f]]. I can *)
(* avoid a case analysis by observing that in both *)
(* cases, the value that satisfies a literal [[lit]] is *)
(* equal to \monobox(symbol? lit).              *)
(* <boxed values 160>=                          *)
val _ = op eqType  : ty      * ty      -> bool
val _ = op eqTypes : ty list * ty list -> bool
(* <substitutions for \mcl>=                    *)
type rootsubst = (modident * path) list
val idsubst = []
(* <boxed values 161>=                          *)
type rootsubst = rootsubst
val _ = op idsubst : rootsubst
(* <substitutions for \mcl>=                    *)
infix 7 |-->
fun id |--> p = [(id, p)]
(* <boxed values 162>=                          *)
val _ = op |--> : modident * path -> rootsubst
(* <substitutions for \mcl>=                    *)
type tysubst = (path * ty) list
fun associatedWith (x, []) =
      NONE
  | associatedWith (x, (key, value) :: pairs) =
      if x = key then SOME value else associatedWith (x, pairs)

fun hasKey [] x = false
  | hasKey ((key, value) :: pairs) x = x = key orelse hasKey pairs x
(* <boxed values 163>=                          *)
type tysubst = tysubst
val _ = op associatedWith : path * tysubst -> ty option
val _ = op hasKey : tysubst -> path -> bool
(* <substitutions for \mcl>=                    *)
fun pathsubstRoot theta =
  let fun subst (PNAME id) =
            (case List.find (fn (id', p') => id = id') theta
               of SOME (_, p) => p
                | NONE => PNAME id)
        | subst (PDOT (p, x)) = PDOT (subst p, x)
        | subst (PAPPLY (p, ps)) = PAPPLY (subst p, map subst ps)
  in  subst
  end
(* <boxed values 164>=                          *)
val _ = op pathsubstRoot : rootsubst -> path -> path
(* <substitutions for \mcl>=                    *)
fun tysubstRoot theta (TYNAME p)          = TYNAME (pathsubstRoot theta p)
  | tysubstRoot theta (FUNTY (args, res)) =
      FUNTY (map (tysubstRoot theta) args, tysubstRoot theta res)
  | tysubstRoot theta ANYTYPE = ANYTYPE
(* <boxed values 165>=                          *)
val _ = op tysubstRoot : rootsubst -> ty -> ty
(* <substitutions for \mcl>=                    *)
fun dom theta = map (fn (a, _) => a) theta
fun compose (theta2, theta1) =
  let val domain  = union (dom theta2, dom theta1)
      val replace = pathsubstRoot theta2 o pathsubstRoot theta1 o PNAME
  in  map (fn a => (a, replace a)) domain
  end
(* <boxed values 166>=                          *)
val _ = op dom     : rootsubst -> modident set
val _ = op compose : rootsubst * rootsubst -> rootsubst
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <substitutions for \mcl>=                    *)
fun bsubstRoot s = 
  map (fn (x, a) => (x, s a))

fun mtsubstRoot theta =
  let fun s (MTEXPORTS comps)     = MTEXPORTS (bsubstRoot (compsubstRoot theta)
                                                                          comps)
        | s (MTALLOF mts)         = MTALLOF (map s mts)
        | s (MTARROW (args, res)) = MTARROW (bsubstRoot s args, s res)
  in  s
  end
and compsubstRoot theta =
  let fun s (COMPVAL t) = COMPVAL (tysubstRoot theta t)
        | s (COMPABSTY path) = COMPABSTY (pathsubstRoot theta path)
        | s (COMPMANTY t)  = COMPMANTY (tysubstRoot theta t)
        | s (COMPMOD mt)  = COMPMOD (mtsubstRoot theta mt)
  in  s
  end
(* <boxed values 167>=                          *)
val _ = op mtsubstRoot   : rootsubst -> modty      -> modty
val _ = op compsubstRoot : rootsubst -> component -> component
(* <substitutions for \mcl>=                    *)
fun tysubstManifest mantypes =
  let fun r (TYNAME path) = getOpt (associatedWith (path, mantypes), TYNAME path
                                                                               )
        | r (FUNTY (args, res)) = FUNTY (map r args, r res)
        | r (ANYTYPE) = ANYTYPE
  in  r
  end
(* <boxed values 168>=                          *)
val _ = op tysubstManifest : tysubst -> ty -> ty
(* <substitutions for \mcl>=                    *)
fun mtsubstManifest mantypes mt =
  let val newty = tysubstManifest mantypes
      fun newmt (MTEXPORTS cs) = MTEXPORTS (map (fn (x, c) => (x, newcomp c)) cs
                                                                               )
        | newmt (MTALLOF mts)  = MTALLOF (map newmt mts)
                                             (* can't violate unmix invariant *)
        | newmt (MTARROW (args, result)) =
            MTARROW (map (fn (x, mt) => (x, newmt mt)) args, newmt result)
      and newcomp (COMPVAL tau) = COMPVAL (newty tau)
        | newcomp (COMPABSTY p) =
           (case associatedWith (p, mantypes)
              of SOME tau => COMPMANTY tau
               | NONE => COMPABSTY p)   (* used to be this on every path *)
        | newcomp (COMPMANTY tau) = COMPMANTY (newty tau)
        | newcomp (COMPMOD mt) = COMPMOD (newmt mt)
  in  newmt mt
  end
(* <boxed values 169>=                          *)
val _ = op mtsubstManifest : tysubst -> modty -> modty
(* <type components of module types>=           *)
fun abstractTypePaths (MTEXPORTS cs, path : path) =
      let fun mts (t, COMPABSTY _) = [PDOT (path, t)]
            | mts (x, COMPMOD mt) = abstractTypePaths (mt, PDOT (path, x))
            | mts _ = []
(* An invariant on combined module types        *)
(*                                              *)
(* Important invariant of the least upper bound: In any *)
(* semantic [[MTALLOF]], if a type name appears as *)
(* manifest in any alternative, it appears only as *)
(* manifest, never as abstract—and the module type has *)
(* no references to an abstract type of that name. *)
(*                                              *)
(* Violations of this invariant are detected by function *)
(* [[mixedManifestations]].                     *)
(* <boxed values 130>=                          *)
val _ = op abstractTypePaths : modty rooted -> path list
      in  (List.concat o map mts) cs
      end
  | abstractTypePaths (MTALLOF mts, path) =
      (List.concat o map (fn mt => abstractTypePaths (mt, path))) mts
  | abstractTypePaths (MTARROW _, _) = []
                                          (* could be bogus, cf Leroy rule 21 *)
(* Realization                                  *)
(*                                              *)
(* This general-purpose code ought to go elsewhere. *)
(* <utilities for module-type realization>=     *)
fun filterdec p (MTARROW f, path) = MTARROW f
  | filterdec p (MTALLOF mts, path) = MTALLOF (map (fn mt => filterdec p (mt,
                                                                     path)) mts)
  | filterdec p (MTEXPORTS xcs, path) =
      let fun cons ((x, c), xcs) =
            let val path = PDOT (path, x)
                val c = case c of COMPMOD mt => COMPMOD (filterdec p (mt, path))
                                | _ => c
            in  if p (c, path) then
                  (x, c) :: xcs
                else
                  xcs
            end
      in  MTEXPORTS (foldr cons [] xcs)
      end
(* <utilities for module-type realization>=     *)
fun emptyExports (MTEXPORTS []) = true
  | emptyExports _ = false

(* <module-type realization>=                   *)
fun manifestSubsn (MTEXPORTS cs, path) =
      let fun mts (x, COMPMANTY tau) = [(PDOT (path, x), tau)]
            | mts (x, COMPMOD mt) = manifestSubsn (mt, PDOT(path, x))
            | mts _ = []
      in  (List.concat o map mts) cs
      end
  | manifestSubsn (MTALLOF mts, path) =
      (List.concat o map (fn mt => manifestSubsn (mt, path))) mts
  | manifestSubsn (MTARROW _, path) = []
                                          (* could be bogus, cf Leroy rule 21 *)
(* NOT CLEAR IF THIS BELONGS HERE OR IN SUPPLEMENT. *)
(* <boxed values 133>=                          *)
val _ = op manifestSubsn : modty rooted -> tysubst
(* This is purely a heuristic to get things looking *)
(* nice. We filter out redundant manifest-type  *)
(* declarations, and we drop any argument that consists *)
(* only of redundant declarations (or is otherwise *)
(* empty).                                      *)
(* <module-type realization>=                   *)
val simpleSyntacticMeet : modty -> modty =
  let val path = PNAME (MODTYPLACEHOLDER "syntactic meet")
      fun filterManifest (prev', []) = rev prev'
        | filterManifest (prev', mt :: mts) =
            let val manifests = manifestSubsn (MTALLOF prev', path)
                fun redundant (COMPMANTY tau, p) =
                      (case associatedWith (p, manifests)
                         of SOME tau' => eqType (tau, tau')
                          | NONE => false)
                  | redundant _ = false
            in  filterManifest (filterdec (not o redundant) (mt, path) :: prev',
                                                                            mts)
            end
      val filterManifest = fn mts => filterManifest ([], mts)
      fun mtall [mt] = mt
        | mtall mts  = MTALLOF mts
      val meet = mtall o List.filter (not o emptyExports) o filterManifest
  in  fn (MTALLOF mts) => meet mts
       | mt => mt
  end
(* It establishes this invariant: In any semantic *)
(* [[MTALLOF]], if a type name appears as manifest in *)
(* any alternative, it appears only as manifest, never *)
(* as abstract—and the module type has no references to *)
(* an abstract type of that name.               *)
(* <module-type realization>=                   *)
fun allofAt (mts, path) =  (* smart constructor, rooted module type *)
  let val mt = MTALLOF mts
      val mantypes = manifestSubsn (mt, path)
      val abstypes = abstractTypePaths (mt, path)
  in  if List.exists (hasKey mantypes) abstypes then
        simpleSyntacticMeet (mtsubstManifest mantypes mt)
      else
        mt
  end
(* <module-type realization>=                   *)
fun unmixTypes (mt, path) =
  let fun mtype (MTEXPORTS cs) = MTEXPORTS (map comp cs)
        | mtype (MTALLOF mts)  = allofAt (map mtype mts, path)
        | mtype (MTARROW (args, result)) =
            MTARROW (map (fn (x, mt) => (x, mtype mt)) args, mtype result)
      and comp (x, COMPMOD mt) = (x, COMPMOD (unmixTypes (mt, PDOT (path, x))))
        | comp c = c
  in  mtype mt
  end
(* Restores the invariant at need.              *)
(* <boxed values 170>=                          *)
val _ = op unmixTypes : modty rooted -> modty
(* <invariants of \mcl>=                        *)
fun mixedManifestations mt =
  let val path = PNAME (MODTYPLACEHOLDER "invariant checking")
      val manifests = manifestSubsn (mt, path)
      val abstracts = abstractTypePaths (mt, path)
  in  List.exists (hasKey manifests) abstracts
  end
(* <[[implements]] relation, based on [[subtype]] of two module types>= *)
infix 1 >>
fun (OK ()) >> c = c
  | (ERROR msg) >> _ = ERROR msg

fun allE []      = OK ()
  | allE (e::es) = e >> allE es

fun subtype mts =
  let fun st (MTARROW (args, res), MTARROW (args', res')) =
            unimp "subtyping on arrow modules -- need to make reflexive"
        | st (MTARROW (args, _), _) =
            ERROR ("expected an exporting module but got one that takes " ^
                   countString args "parameter")
        | st (_, MTARROW (args, _)) =
            ERROR ("expected a module that takes " ^
                   countString args "parameter" ^
                                                ", but got an exporting module")
        | st (mt, MTALLOF mts') =
            allE (map (fn mt' => st (mt, mt')) mts')
        | st (mt, MTEXPORTS comps') =
            compsSubtype (components mt, comps')
      and components (MTEXPORTS cs) = cs
        | components (MTALLOF mts) = List.concat (map components mts)
        | components (MTARROW _) = raise InternalError "meet of arrow types"
      and compsSubtype (comps, comps') =
            let fun supplied (x, _) = List.exists (fn (y, _) => x = y) comps
                val (present, absent) = List.partition supplied comps'
                fun check (x, supercomp) =
                  let (* <definition of [[csubtype]]>=                *)
                      fun csubtype (COMPVAL tau, COMPVAL tau') =
                            if eqType (tau, tau') then OK ()
                            else ERROR ("interface calls for value " ^ x ^
                                                              " to have type " ^
                                        typeString tau' ^ ", but it has type " ^
                                                                 typeString tau)
                        | csubtype (COMPABSTY _, COMPABSTY _) = OK ()
                                   (* XXX really OK? without comparing paths? *)
                        | csubtype (COMPMANTY _, COMPABSTY _) = OK ()
                                                             (* XXX likewise? *)
                        | csubtype (COMPMANTY tau, COMPMANTY tau') = 
                            if eqType (tau, tau') then OK ()
                            else ERROR ("interface calls for type " ^ x ^
                                                       " to manifestly equal " ^
                                        typeString tau' ^ ", but it is " ^
                                                                 typeString tau)
                        | csubtype (COMPABSTY path, COMPMANTY tau') =
                            if eqType (TYNAME path, tau') then OK ()
                            else ERROR ("interface calls for type " ^ x ^
                                                       " to manifestly equal " ^
                                        typeString tau' ^ ", but it is " ^
                                                       typeString (TYNAME path))
                        | csubtype (COMPMOD m, COMPMOD m') =
                            subtype (m, m')
                        | csubtype (c, c') =
                            ERROR ("interface calls for " ^ x ^ " to be " ^
                                                                   whatcomp c' ^
                                   ", but implementation provides " ^ whatcomp c
                                                                               )
                      (* THIS ONE LOOKS GOOD AND IMPORTANT            *)
                      (* <boxed values 132>=                          *)
                      val _ = op csubtype : component * component -> unit error
(* Module subtyping                             *)
(*                                              *)
(* MUST UNDERSTAND LEROY'S SUBSTITUTIONS HERE.  *)
(*                                              *)
(* IDEAS:                                       *)
(*                                              *)
(*   • Witness to lack of subtype should be keyed by *)
(*  path.                                       *)
(*   • Error message should tell the whole story, e.g., *)
(*  ``context requires that [[t]] be both [[int]] and *)
(*  [[bool]].''                                 *)
(*   • Try a cheap and cheerful solution to uninhabited *)
(*  intersections, e.g., incompatible manifest types? *)
(*                                              *)
(* <boxed values 131>=                          *)
val _ = op csubtype : component * component -> unit error
val _ = op subtype  : modty * modty -> unit error
                  in  csubtype (find (x, comps), supercomp)
                  end
                    handle NotFound y => raise InternalError
                                                      "missed present component"
                val missedMsg =
                  if null absent then OK ()
                  else
                    ERROR (
                    "an interface expected some components that are missing: " ^
                           commaSep
                           (map (fn (x, c) => x ^ " (" ^ whatcomp c ^ ")")
                                                                        absent))
            in  allE (map check present) >> missedMsg
            end
  in  st mts
  end
(* KEY THING! This is my approximation of Leroy's *)
(* [[modtype_match]]. Instead of placing type equalities *)
(* in an environment, I substitute. The ice is getting *)
(* thin here.                                   *)
(* <[[implements]] relation, based on [[subtype]] of two module types>= *)
val mtsubstManifestDebug = fn theta => fn (super, p) =>
  let val mt' = mtsubstManifest theta super
      val () = app eprint [countString theta "substitution", "\n"]
      val () = app (fn (pi, tau) => app eprint ["   ", pathString pi, " |--> ",
                                                    typeString tau, "\n"]) theta
      val () = app eprint ["realized: ", mtString mt', "\n"]
      
  in  mt'
  end
fun implements (p : path, submt, supermt) =
 (*   (app eprint ["At ", pathString p,
                   "\n  sub:  ", mtString submt, "\n  sup: ", mtString supermt,
                                                                      "\n"]; id)
  *)
  let val theta = manifestSubsn (submt, p)
  in  subtype (submt, mtsubstManifest theta supermt)  (* XXX need unmixTypes? *)
  end
(* <path-expression lookup>=                    *)
fun asBinding (COMPVAL tau, root) = ENVVAL tau
  | asBinding (COMPABSTY path, root) = ENVMANTY (TYNAME path)
  | asBinding (COMPMANTY tau, root) = ENVMANTY tau
  | asBinding (COMPMOD mt, root) = ENVMOD (mt, root)

fun uproot (ENVVAL tau) = COMPVAL tau
  | uproot (ENVMANTY tau) = COMPMANTY tau
  | uproot (ENVMOD (mt, _)) = COMPMOD mt
  | uproot d = raise InternalError (whatdec d ^ " as component")

fun notModule (dcl, px) =
  raise TypeError ("looking for a module, but " ^ pathexString px ^
                   " is a " ^ whatdec dcl)
fun pathfind (PNAME x, Gamma) = find (snd x, Gamma)
  | pathfind (PDOT (path, x), Gamma) =
      let (* <definition of [[mtfind]]>=                  *)
          fun mtfind (x, mt as MTEXPORTS comps) : component option =
                 (SOME (find (x, comps)) handle NotFound _ => NONE)
            | mtfind (x, MTARROW _) =
                 raise TypeError ("tried to select component " ^ x ^
                                  " from generic module " ^ pathexString path)
            | mtfind (x, mt as MTALLOF mts) =
                (case List.mapPartial (fn mt => mtfind (x, mt)) mts
                   of [comp] => SOME comp
                    | [] => NONE
                    | _ :: _ :: _ => unimp "component in multiple signatures")
          fun noComponent (path, x, mt) =
            raise TypeError ("module " ^ pathexString path ^
                                                 " does not have a component " ^
                             pathexString (PDOT (path, x)) ^ "; its type is " ^
                                                                    mtString mt)
          (* <boxed values 135>=                          *)
          val _ = op mtfind : name * modty -> component option
      in  case pathfind (path, Gamma)
            of ENVMOD (mt, root) =>
                 (asBinding (valOf (mtfind (x, mt)), root) handle Option =>
                   noComponent (path, x, mt))
             | dec =>
               (* <tried to select [[path]].[[x]] but [[path]] is a [[dec]]>= *)
                      raise TypeError ("Tried to select " ^ pathexString (PDOT (
                                                          path, x)) ^ ", but " ^
                                       pathexString path ^ " is " ^ whatdec dec
                                                         ^ ", which does not " ^
                                       " have components")
      end
  | pathfind (PAPPLY (fpx, actualpxs) : pathex, Gamma) =
     (* This is Leroy's [[Apply]] rule. The idea is  *)
     (* summarized as follows: {mathpar} f : PiA:T.B *)
     (*                                              *)
     (* f @@ M : B[A |->M] {mathpar} This works even if B is *)
     (* itself an arrow type. Uncurrying, it means that when *)
     (* substituting for the first formal parameter, *)
     (* we substitute in all the remaining formal parameters. *)
     (* <instantiation of module [[fpx]] to [[actualpxs]]>= *)
     let fun rootedModtype px = case pathfind (px, Gamma)
                                  of ENVMOD (mt, root) => (mt, root)
                                   | dec => notModule (dec, px)
         val (fmod, actuals) = (rootedModtype fpx, map rootedModtype actualpxs)
         val (formals, result) = case fmod
                                   of (MTARROW fr, _) => fr
                                    | _ =>
                              (* Instantiation                                *)

                              (*                                              *)

                              (* <instantiated exporting module [[fpx]]>=     *)
                                           raise TypeError ("module " ^
                       pathexString fpx ^ " is an exporting module, and only " ^

                                        " a generic module can be instantiated")
         fun resty ([],                               [],
                                                                result) = result
           | resty ((formalid, formalmt) :: formals, (actmt, actroot) :: actuals
                                                                     , result) =
               let val theta = formalid |--> actroot
                   fun fsubst (ident, mt) = (ident, mtsubstRoot theta mt)
                   val mtheta = manifestSubsn (actmt, actroot)
                   val () = if true orelse null mtheta then ()
                     else app (fn (pi, tau) => app eprint ["manifestly ",
                          pathString pi, " |--> ", typeString tau, "\n"]) mtheta
                   val subst = mtsubstManifest mtheta o mtsubstRoot theta
                   (* XXX need to substitute manifest types from the actuals? *)
               in  case implements (actroot, actmt, mtsubstRoot theta formalmt)
                     of OK () => resty (map fsubst formals, actuals, subst
                                                                         result)
                      | ERROR msg =>
                      (* <can't pass [[actroot]] as [[formalid]] to [[fpx]]>= *)
                                     raise TypeError ("module " ^ pathString
                                      actroot ^ " cannot be used as argument " ^
                                                      modidentString formalid ^
                                      " to generic module " ^ pathexString fpx ^
                                                      ": " ^ msg)
               end
           | resty _ = (* <wrong number of arguments to [[fpx]]>=      *)
                       raise TypeError ("generic module " ^ pathexString fpx ^
                                                              " is expecting " ^
                                        countString formals "parameter" ^
                                                                  ", but got " ^
                                        countString actuals "actual parameter")
     in  ENVMOD (resty (formals, actuals, result), PAPPLY (root fmod, map root
                                                                       actuals))
     end
(* Looking up path expressions                  *)
(*                                              *)
(* <boxed values 134>=                          *)
val _ = op pathfind   : pathex * binding env -> binding
val _ = op asBinding : component * path -> binding
val _ = op uproot : binding -> component

fun addloc loc (PNAME x) = PNAME (loc, x)
  | addloc loc (PDOT (path, x)) = PDOT (addloc loc path, x)
  | addloc loc (PAPPLY _) = raise InternalError "application vcon"

fun vconfind (k, Gamma) = pathfind (addloc ("bogus", ~99) k, Gamma)
(* <translation of {\mcl} type syntax into types>= *)
fun txpath (px, Gamma) =
  let fun tx (PAPPLY (f, args)) = PAPPLY (tx f, map tx args)
        | tx (PDOT (p, x)) = PDOT (tx p, x)
        | tx (PNAME (loc, m)) =
            let fun bad aThing =
                  raise TypeError ("I was expecting " ^ m ^
                                                     " to refer to a module, " ^
                                   "but at " ^ srclocString loc ^ ", it's " ^
                                                                         aThing)
            in  case find (m, Gamma)
                  of ENVMODTY _ => bad "a module type"
                   | ENVMOD (mt, p) => p
                   | c => bad (whatdec c)
            end
  in  tx px
  end
val elabpath = txpath
(* Translation/elaboration of syntax into types *)
(*                                              *)
(* We translate paths, types, declarations, and module *)
(* types.                                       *)
(* <boxed values 171>=                          *)
val _ = op txpath : pathex * binding env -> path
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <translation of {\mcl} type syntax into types>= *)
fun elabty (t, Gamma) =
  let fun tx (TYNAME px) =
            (case pathfind (px, Gamma)
               of ENVMANTY tau => tau
                | dec => raise TypeError ("I was expecting a type, but " ^
                                           pathexString px ^ " is " ^ whatdec
                                                                           dec))
        | tx (FUNTY (args, res)) = FUNTY (map tx args, tx res)
        | tx ANYTYPE = ANYTYPE
  in  tx t
  end
(* <boxed values 172>=                          *)
val _ = op elabty : tyex * binding env -> ty
(* <translation of {\mcl} type syntax into types>= *)
fun findModty (x, Gamma) =
  case find (x, Gamma)
    of ENVMODTY mt => mt
     | dec => raise TypeError ("Tried to use " ^ whatdec dec ^ " " ^ x ^
                                " as a module type")
(* <boxed values 173>=                          *)
val _ = op findModty : name * binding env -> modty
(* <translation of {\mcl} type syntax into types>= *)
fun elabmt ((mtx : modtyx, path), Gamma) =
  let val resultName = PNAME (MODTYPLACEHOLDER "functor result")
      fun tx (MTNAMEDX t) = mtsubstRoot (MODTYPLACEHOLDER t |--> path) (
                                                           findModty (t, Gamma))
        | tx (MTEXPORTSX exports) =
             let val (this', _) = foldl (leftLocated export) ([], Gamma) exports
             in  MTEXPORTS (rev this')
             end
        | tx (MTALLOFX mts) = allofAt (map (located tx) mts, path)
        | tx (MTARROWX (args, body)) =
            let fun txArrow ([], (loc, body), Gamma : binding env) =
                      ([], atLoc loc elabmt ((body, resultName), Gamma))
                  | txArrow (((mloc, m), (mtloc, mtx)) :: rest, body, Gamma) =
                      let val modid = genmodident m
                          val modty = atLoc mtloc elabmt ((mtx, PNAME modid),
                                                                          Gamma)
                          val () =
                             (* <if [[modty]] is generic, bleat about [[m]]>= *)
                                   case modty
                                     of MTARROW _ =>
                                       raise TypeError ("module parameter " ^ m
                                               ^ " is generic, but a generic " ^

                    "module may not take another generic module as a parameter")
                                      | _ => ()
                          val Gamma' = bind (m, ENVMOD (modty, PNAME modid),
                                                                          Gamma)
                             (* XXX check 1st arg to ENVMOD *)
                          val (rest', body') = txArrow (rest, body, Gamma')
                      in  ((modid, modty) :: rest', body')
                      end
            in  MTARROW (txArrow (args, body, Gamma))
            end

      and export ((x, ctx : decl), (theseDecls, Gamma)) =
            if isbound (x, theseDecls) then
              raise TypeError ("duplicate declaration of " ^ x ^
                                                              " in module type")
            else
              let val c = txComp ((ctx, PDOT (path, x)), Gamma)
              in  ((x, c) :: theseDecls, bind (x, asBinding (c, path), Gamma))
              end
(* <boxed values 174>=                          *)
val _ = op elabmt : modtyx rooted * binding env -> modty
  in  tx mtx
  end
(* <translation of {\mcl} type syntax into types>= *)
and txComp ((comp : decl, path), Gamma : binding env) : component =
  let fun ty t = elabty (t, Gamma)
(* <boxed values 175>=                          *)
val _ = op txDecl    : decl rooted * binding env -> binding
val _ = op txComp    : decl rooted * binding env -> component
  in  case comp
        of DECVAL tau  => COMPVAL (ty tau)
         | DECABSTY    => COMPABSTY path
         | DECMANTY t  => COMPMANTY (ty t)
         | DECMOD mt   => COMPMOD (elabmt ((mt, path), Gamma))
                              (* XXX is path really OK here??? *)
         | DECMODTY mt =>
             raise TypeError ("module type " ^ pathString path ^
                                    " may not be a component of another module")
  end
and txDecl ((comp : decl, path), Gamma : binding env) : binding =
  let fun ty t = elabty (t, Gamma)
  in  case comp
        of DECVAL tau  => ENVVAL (ty tau)
         | DECABSTY    => ENVMANTY (TYNAME path)
         | DECMANTY t  => ENVMANTY (ty t)
         | DECMOD mt   => ENVMOD (elabmt ((mt, path), Gamma), path)
                              (* XXX is path really OK here??? *)
         | DECMODTY mt => ENVMODTY (elabmt ((mt, path), Gamma))
  end
val elabmt = fn a =>
  let val mt = elabmt a
  in  if mixedManifestations mt then
        raise BugInTypeChecking ("invariant violation (mixed M): " ^ mtString mt
                                                                               )
      else
        mt
  end
(* The initial basis                            *)
(*                                              *)
(* <primitive modules and types used to type literal expressions>= *)
val arraymodname = "Array"

val intmodident = genmodident "Int"
val symmodident = genmodident "Sym"
val boolmodident = genmodident "Bool"
val unitmodident = genmodident "Unit"
val arraymodident = genmodident arraymodname
val uarraymodident = genmodident "UnsafeArray"

val inttype = TYNAME (PDOT (PNAME intmodident, "t"))
val symtype = TYNAME (PDOT (PNAME symmodident, "t"))
val booltype = TYNAME (PDOT (PNAME boolmodident, "t"))
val unittype = TYNAME (PDOT (PNAME unitmodident, "t"))

fun arraytype tau =
  case tau
    of TYNAME (PDOT (module, "t")) =>
         TYNAME (PDOT (PAPPLY (PNAME arraymodident, [module]), "t"))
     | _ => raise InternalError "unable to form internal array type"


fun addValWith f ((x, v, ty), rho) = bind (x, f v, rho)
fun decval (x, v, ty) = (x, ENVVAL ty)
fun compval (x, v, ty) = (x, COMPVAL ty)


(* <shared utility functions for building primitives in languages with type checking>= *)
fun binaryOp f = (fn [a, b] => f (a, b) | _ => raise BugInTypeChecking "arity 2"
                                                                               )
fun unaryOp  f = (fn [a]    => f a      | _ => raise BugInTypeChecking "arity 1"
                                                                               )
(* Here are the primitives. As in Chapter [->], all are *)
(* either binary or unary operators. Type checking *)
(* should guarantee that operators are used with the *)
(* correct arity.                               *)
(* <boxed values 296>=                          *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
(* <shared utility functions for building primitives in languages with type checking>= *)
fun arithOp f =
      binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                 | _ => raise BugInTypeChecking "arithmetic on non-numbers")
(* Arithmetic primitives expect and return integers. *)
(* <boxed values 297>=                          *)
val _ = op arithOp   : (int * int -> int) -> (value list -> value)
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <primitives ((mcl))>=                        *)
fun eqPrintPrims tau strip =
  let val comptype = FUNTY ([tau, tau], booltype)
      fun comparison f = binaryOp (embedBool o (fn (x, y) => f (strip x, strip y
                                                                             )))
  in  ("similar?",  comparison op =,  comptype) ::
      ("dissimilar?",  comparison op =,  comptype) ::
      ("=",  comparison op =,  comptype) ::
      ("!=", comparison op <>, comptype) ::
      ("print", unaryOp (fn x => (print (valueString x);unitVal)), FUNTY ([tau],
                                                                   unittype)) ::
      ("println", unaryOp (fn x => (println (valueString x);unitVal)), FUNTY ([
                                                             tau], unittype)) ::
      []
  end

val symPrims =
  eqPrintPrims symtype (fn SYM s => s | _ => raise BugInTypeChecking
                                                        "comparing non-symbols")

val boolPrims =
  eqPrintPrims booltype (fn CONVAL (K, []) => K
                          | _ => raise BugInTypeChecking
                                                       "comparing non-Booleans")

(* <primitives ((mcl))>=                        *)
fun comparison f = binaryOp (embedBool o f)
fun intcompare f = 
      comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                   | _ => raise BugInTypeChecking "comparing non-numbers")

fun asInt (NUM n) = n
  | asInt v = raise BugInTypeChecking ("expected a number; got " ^ valueString v
                                                                               )

val arithtype = FUNTY ([inttype, inttype], inttype)
val comptype  = FUNTY ([inttype, inttype], booltype)

fun wordOp f = arithOp (fn (n, m) => Word.toInt (f (Word.fromInt n, Word.fromInt
                                                                            m)))
fun unaryIntOp f = unaryOp (NUM o f o asInt)
fun unaryWordOp f = unaryIntOp (Word.toInt o f o Word.fromInt)


val intPrims = 
  ("+", arithOp op +,   arithtype) :: 
  ("-", arithOp op -,   arithtype) :: 
  ("*", arithOp op *,   arithtype) :: 
  ("/", arithOp op div, arithtype) ::

  ("land", wordOp Word.andb, arithtype) ::
  ("lor", wordOp Word.orb, arithtype) ::
  (">>u", wordOp Word.>>, arithtype) ::
  (">>s", wordOp Word.~>>, arithtype) ::
  ("<<",  wordOp Word.<<, arithtype) ::

  ("of-int", unaryOp id,             FUNTY ([inttype], inttype)) ::
  ("negated", unaryIntOp ~,          FUNTY ([inttype], inttype)) ::
  ("lnot", unaryWordOp Word.notb, FUNTY ([inttype], inttype)) ::

  ("<",  intcompare op <,  comptype) :: 
  (">",  intcompare op >,  comptype) ::
  ("<=", intcompare op <=, comptype) :: 
  (">=", intcompare op >=, comptype) ::
  ("printu", unaryOp (fn n => (printUTF8 (asInt n); unitVal)), FUNTY ([inttype],
                                                                   unittype)) ::
  eqPrintPrims inttype (fn NUM n => n | _ => raise BugInTypeChecking
                                                        "comparing non-numbers")
(* <primitives ((mcl))>=                        *)
local
  val arraypath = PNAME arraymodident
  val arrayarg  = genmodident "Elem"
  val argpath   = PNAME arrayarg
  val resultpath = PAPPLY (arraypath, [argpath])
  val elemtype   = TYNAME (PDOT (argpath, "t"))
  val arraytype  = TYNAME (PDOT (resultpath, "t"))


  fun protect f x = f x
    handle Size      => raise RuntimeError "array too big"
         | Subscript => raise RuntimeError "array index out of bounds"


  fun asArray (ARRAY a) = a
    | asArray _         = raise BugInTypeChecking "non-array value as array"
  fun arrayLeft f (a, x) = f (asArray a, x)
in
  val arrayPrims = 
    ("size", unaryOp (NUM o Array.length o asArray), FUNTY ([arraytype], inttype
                                                                           )) ::
    ("new", binaryOp (fn (NUM n, a) => ARRAY (protect Array.array (n, a))
                       | _ => raise BugInTypeChecking "array size not a number")
                                                                               ,
            FUNTY ([inttype, elemtype], arraytype)) ::
    ("empty", fn _ => ARRAY (Array.fromList []), FUNTY ([], arraytype)) ::
    ("at", binaryOp (fn (ARRAY a, NUM i) => protect Array.sub (a, i)
                      | _ => raise BugInTypeChecking "Array.at array or index"),
            FUNTY ([arraytype, inttype], elemtype)) ::
    ("at-put", fn [ARRAY a, NUM i, x] => (protect Array.update (a, i, x);
                                                                        unitVal)
                | _ => raise BugInTypeChecking
                                      "number or types of args to Array.at-put",
            FUNTY ([arraytype, inttype, elemtype], unittype)) ::
    []

  val arraymodtype : modty =
    MTARROW ([(arrayarg, MTEXPORTS [("t", COMPABSTY (PDOT (argpath, "t")))]  :
                                                                        modty)],
             MTEXPORTS (("t", COMPABSTY (PDOT (resultpath, "t"))) ::
                        ("elem", COMPMANTY elemtype) ::
                        map compval arrayPrims) : modty)

  val uarrayPrims = 
    ("new", unaryOp (fn (NUM n) => ARRAY (protect Array.array (n, CONVAL (PNAME
                                                          "uninitialized", [])))
                       | _ => raise BugInTypeChecking "array size not a number")
                                                                               ,
            FUNTY ([inttype], arraytype)) ::
    []

  val uarraymodtype : modty =
    MTARROW ([(arrayarg, MTEXPORTS [("t", COMPABSTY (PDOT (argpath, "t")))]  :
                                                                        modty)],
             MTEXPORTS (("t", COMPABSTY (PDOT (resultpath, "t"))) ::
                        map compval uarrayPrims) : modty)
end
(* <primitives ((mcl))>=                        *)
fun inject_bool x =
      CONVAL (PNAME (if x then "#t" else "#f"), [])
fun project_bool (CONVAL (PNAME "#t", [])) = true
  | project_bool (CONVAL (PNAME "#f", [])) = false
  | project_bool _ = raise RuntimeError "projected non-boolean"

fun inject_predicate f = fn x => inject_bool (f x)
fun predop f = unaryOp (inject_predicate f)

fun comparison f = binaryOp (inject_predicate f)
fun intcompare f = comparison (
                     fn (NUM n1, NUM n2) => f (n1, n2)
                      | _ => raise BugInTypeChecking "integers expected")
(* <boxed values 196>=                          *)
val _ = op inject_bool  : bool -> value
val _ = op project_bool : value -> bool
(* And here come the predicates. Equality comparison *)
(* succeeds only on symbols and numbers. The empty list *)
(* is dealt with through [[case]] expressions.  *)


val unitval = 
  ("unit", CONVAL (PNAME "unit", []), TYNAME (PDOT (PNAME unitmodident, "t")))

local
  fun module id primvals : binding =
    ENVMOD (MTEXPORTS (("t", COMPABSTY (PDOT (PNAME id, "t"))) :: map compval
                                                                      primvals),
            PNAME id)
in
  val intmod  = module intmodident intPrims
  val symmod  = module symmodident symPrims
  val boolmod = module boolmodident boolPrims
  val unitmod = module unitmodident [unitval]
  val arraymod  = ENVMOD (arraymodtype, PNAME arraymodident)
  val uarraymod  = ENVMOD (uarraymodtype, PNAME uarraymodident)
end

(* Type checking for expressions                *)
(*                                              *)
(* Here's how operator overloading works:       *)
(*                                              *)
(*   • An overloaded name is associated with a sequence *)
(*  of values: one for each type at which the name is *)
(*  overloaded.                                 *)
(*   • At run time, the sequence is represented by an *)
(*  array of values.                            *)
(*   • At compile time, the sequence is represented by a *)
(*  list of types.                              *)
(*   • Adding an overloading means consing on to the *)
(*  front of the sequence.                      *)
(*   • Using an overloaded name requires an index into *)
(*  the sequence. The first matching type wins. *)
(*   • An overloaded name can be used only in a function *)
(*  application. At every application, therefore, the *)
(*  type checker writes the sequence index into the *)
(*  AST node.                                   *)
(*                                              *)
(* <utility functions on {\mcl} types>=         *)
fun firstArgType (x, FUNTY (tau :: _, _)) = OK tau
  | firstArgType (x, FUNTY ([], _)) =
      ERROR ("function " ^ x ^
                 " cannot be overloaded because it does not take any arguments")
  | firstArgType (x, _) =
      ERROR (x ^ " cannot be overloaded because it is not a function")

(* <utility functions on {\mcl} types>=         *)
fun okOrTypeError (OK a) = a
  | okOrTypeError (ERROR msg) = raise TypeError msg

fun ok a = okOrTypeError a handle _ => raise InternalError
                                                      "overloaded non-function?"
fun resolveOverloaded (f, argty : ty, tys : ty list) : (ty * int) error =
  let fun findAt (tau :: taus, i) = if eqType (argty, ok (firstArgType (f, tau))
                                                                          ) then
                                      OK (tau, i)
                                    else
                                      findAt (taus, i + 1)
        | findAt ([], _) =
            ERROR ("cannot figure out how to resolve overloaded name " ^ f ^
                   " when applied to first argument of type " ^ typeString argty
                                                                               ^
                   " (resolvable: " ^ separate ("", ", ") (map typeString tys) ^
                                                                            ")")
  in  findAt (tys, 0)
  end
(* <boxed values 137>=                          *)
val _ = op resolveOverloaded : name * ty * ty list -> (ty * int) error
(* <[[typeof]] a {\mcl} expression ((prototype))>= *)
fun typeof (e, Gamma) : ty = raise LeftAsExercise "typeof"
(* <principal type of a module>=                *)
fun strengthen (MTEXPORTS comps, p) =
      let fun comp (c as (x, dc)) =
            case dc
              of COMPABSTY _ => (x, COMPMANTY (TYNAME (PDOT (p, x))))
               | COMPMOD mt  => (x, COMPMOD (strengthen (mt, PDOT (p, x))))
                                                              (* XXX check me *)
               | COMPVAL   _ => c
               | COMPMANTY _ => c
      in  MTEXPORTS (map comp comps)
      end
  | strengthen (MTALLOF mts, p) =
      allofAt (map (fn mt => strengthen (mt, p)) mts, p)
  | strengthen (mt as MTARROW _, p) =
      mt
(* \typesystemmolecule                          *)
(*                                              *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(* {mathpar} \typeise tau                       *)
(*                                              *)
(* \tyrule Case \threeline \typeise tau \typeis\choice *)
(* p_i e_i tau-->tau_i, 1 <=i <=n tau_1 = ...= tau_n \ *)
(* typeis\xcase(e, \choicep_1 e_1, ..., \choicep_n e_n) *)
(* tau_1                                        *)
(*                                              *)
(* \tyrule Vcon Gamma(\avcon) = tau \typeis\avcontau *)
(* \typeis\choicep e tau-->tau'                 *)
(*                                              *)
(* \tyruleChoice \twoquad \pattypeisp Gamma' tau \typeis *)
(* [+Gamma'] e tau' \typeis\choicep e tau-->tau' *)
(* \pattypeisp Gamma' tau                       *)
(*                                              *)
(* \tyrulePatVcon \threeline \typeis\avcon\crossdotsktau *)
(* -->tau \pattypeisp_i Gamma'_i tau_i, 1 <=i <=k Gamma' *)
(* = Gamma'_1 \dunion...\dunionGamma'_k \pattypeis\ *)
(* applyvcon\cdotskp Gamma' tau                 *)
(*                                              *)
(* \tyrulePatBareVcon \typeis\avcontau \pattypeis\avcon\ *)
(* emptyenv tau                                 *)
(*                                              *)
(* \tyrulePatWildcard \pattypeis\astwildcard \emptyenv *)
(* tau                                          *)
(*                                              *)
(* \tyrulePatVar \pattypeisx {x |->tau} tau {mathpar} *)
(*                                              *)
(* Typing rules for monomorphic case expressions, *)
(* choices, and patterns [*]                    *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(*                                              *)
(* Type-checking modules: strengthening         *)
(*                                              *)
(* Is this the principal type of a module?      *)
(* <boxed values 139>=                          *)
val _ = op strengthen : modty rooted -> modty
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun elabDataDef ((T, vcons), context, Gamma) =
  let val tau    = TYNAME (contextDot (context, T))
      val Gamma' = bind (T, ENVMANTY tau, Gamma)
      fun translateVcon (K, tx) =
            (K, elabty (tx, Gamma'))
            handle TypeError msg =>
              raise TypeError ("in type of value constructor " ^ K ^ ", " ^ msg)
      val Ktaus = map translateVcon vcons
        
      fun validate (K, FUNTY (_, result)) =
            if eqType (result, tau) then
              ()
            else 
              (* <result type of [[K]] should be [[tau]] but is [[result]]>= *)
              raise TypeError ("value constructor " ^ K ^ " should return " ^
                                                                typeString tau ^
                               ", but it returns type " ^ typeString result)
        | validate (K, tau') =
            if eqType (tau', tau) then
              ()
            else 
              (* <type of [[K]] should be [[tau]] but is [[tau']]>= *)
              raise TypeError ("value constructor " ^ K ^ " should have " ^
                                                                typeString tau ^
                              ", but it has type " ^ typeString tau')
      val ()     = app validate Ktaus
      val ()     = ()(*addVcons (mu, Ktaus)*)
                                  (* supports exhaustiveness anal. *) (* OMIT *)
  in  (* thin ice here: the type component should be abstract? *)
      (T, ENVMANTY tau) :: map (fn (K, tau) => (K, ENVVAL tau)) Ktaus
  end
(* Elaborating definitions                      *)
(*                                              *)
(* <boxed values 144>=                          *)
val _ = op elabDataDef : data_def * context * binding env -> (name * binding)
                                                                            list
(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun ddString (_, COMPMANTY _) = "*"  (* paper over the thin ice *)
  | ddString (_, COMPVAL tau) = typeString tau
  | ddString _ = raise InternalError "component of algebraic data type"
(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun evalDataDef ((_, typed_vcons), rho) =
  let fun isfuntype (FUNTY _)         = true
        | isfuntype _                 = false
      fun addVcon ((K, t), rho) =
        let val v = if isfuntype t then
                      PRIMITIVE (fn vs => CONVAL (PNAME K, map ref vs))
                    else
                      CONVAL (PNAME K, [])
        in  bind (K, ref v, rho)
        end
(* N.B. Duplicates [[DATA]] case in [[defexps]] XXX. *)
(* <boxed values 145>=                          *)
val _ = op evalDataDef : data_def * value ref env -> value ref env * string list
  in  (foldl addVcon rho typed_vcons, map fst typed_vcons)
  end
(* <elaboration and evaluation of [[data]] definitions for \mcl>= *)
fun asComponent (x, ENVVAL tau) = SOME (x, COMPVAL tau)
  | asComponent (x, ENVMANTY tau) = SOME (x, COMPMANTY tau)
  | asComponent (m, ENVMOD (mt, _)) = SOME (m, COMPMOD mt)
  | asComponent (_, ENVOVLN _) = NONE
  | asComponent (_, ENVMODTY _) = raise InternalError "module type as component"

type basis = binding env * value ref env
fun processDataDef (dd, (Gamma, rho), interactivity) =
  let val bindings      = elabDataDef (dd, TOPLEVEL, Gamma)
      val Gamma'        = Gamma <+> bindings
      val comps         = List.mapPartial asComponent bindings
        (* could convert first component to abstract type here XXX *)
      val (rho', vcons) = evalDataDef (dd, rho)
      val tystrings = map ddString comps
      val _ = if prints interactivity then

         (* <print the new type and each of its value constructors for \mcl>= *)
                let val (T, _) = dd
                    val tau = (case find (T, Gamma')
                                 of ENVMANTY tau => tau
                                  | _ => raise Match)
                              handle _ => raise InternalError
                                                        "datatype is not a type"
                    val (kind, vcon_types) =
                      case tystrings of s :: ss => (s, ss)
                                      | [] => let exception NoKindString in
                                                          raise NoKindString end
                in  ( println (typeString tau ^ " :: " ^ kind)
                    ; ListPair.appEq (fn (K, tau) => println (K ^ " : " ^ tau))
                                                             (vcons, vcon_types)
                    )
                end
              else
                ()
  in  (Gamma', rho')
  end
(* <boxed values 146>=                          *)
val _ = op processDataDef : data_def * basis * interactivity -> basis
(* <elaborate a {\mcl} definition>=             *)
fun declarableResponse c =
      case c
        of ENVMODTY mt => mtString mt
         | ENVVAL tau => typeString tau
         | ENVMANTY _ => "manifest type"
         | ENVMOD (mt, _) => mtString mt
         | ENVOVLN _ => "overloaded name"
(* <elaborate a {\mcl} definition>=             *)
fun printStrings ss _ vs = 
  app print ss
type value_printer = (name -> ty -> value -> unit) -> value list -> unit

fun printMt what m how mt = printStrings [what, " ", m, " ", how, " ", mtString
                                                                             mt]

fun defResponse (x, c) =
  case c
    of ENVVAL tau =>
         (fn printfun => fn [v] => (printfun x tau v; app print [" : ",
                                                                typeString tau])
                          | _ => raise InternalError
                                               "value count for val definition")
     | ENVMANTY tau =>
         let val expansion = typeString tau
         in  if x = expansion then
               printStrings ["abstract type ", x]
             else
               printStrings ["type ", x, " = ", typeString tau]
         end
     | ENVMOD (mt as MTARROW _, _) => printMt "generic module" x ":" mt
     | ENVMOD (mt, _)              => printMt "module" x ":" mt
     | ENVMODTY mt                 => printMt "module type" x "=" mt
     | ENVOVLN _ => raise InternalError "defResponse to overloaded name"
(* <boxed values 141>=                          *)
val _ = op printStrings : string list -> value_printer
val _ = op defResponse : name * binding -> value_printer
(* <elaborate a {\mcl} definition>=             *)
fun defName (VAL (x, _)) = x
  | defName (VALREC (x, _, _)) = x
  | defName (EXP _) = "it"
  | defName (QNAME _) = raise InternalError "defName QNAME"
  | defName (DEFINE (x, _, _)) = x
  | defName (TYPE (t, _)) = t
  | defName (DATA (t, _)) = raise InternalError "defName DATA"
  | defName (OVERLOAD _) = raise InternalError "defName OVERLOAD"
  | defName (MODULE (m, _)) = m
  | defName (GMODULE (m, _, _)) = m
  | defName (MODULETYPE (t, _)) = t

fun defPrinter (d, Gamma) =
      let val x = defName d
      in  defResponse (x, find (x, Gamma))
          handle NotFound _ => raise InternalError "defName not found"
      end
(* <boxed values 142>=                          *)
val _ = op defPrinter : baredef * binding env -> value_printer
(* <elaborate a {\mcl} definition>=             *)
fun findModule (px, Gamma) =
  case pathfind (px, Gamma)
    of ENVMOD (mt, _) => mt
     | dec => raise TypeError ("looking for a module, but " ^ pathexString px ^
                                " is a " ^ whatdec dec)
(* <elaborate a {\mcl} definition>=             *)
(* <more overloading things>=                   *)
fun overloadBinding (p, Gamma) = 
  let val (tau, first) =
        case pathfind (p, Gamma)
          of ENVVAL tau => (tau, okOrTypeError (firstArgType (pathexString p,
                                                                          tau)))
           | c => (* <can't overload a [[c]]>=                    *)
                  raise TypeError ("only functions can be overloaded, but " ^
                                                               whatdec c ^ " " ^
                                   pathexString p ^ " is not a function")
      val x = plast p

      val currentTypes =
        (case find (x, Gamma)
           of ENVOVLN vals => vals
            | _ => []) handle NotFound _ => []
  in  (x, ENVOVLN (tau :: currentTypes))
  end

fun overloadBindings (ps, Gamma) =
  let fun add (bs', Gamma, []) = bs'
        | add (bs', Gamma, p :: ps) =
            let val b = overloadBinding (p, Gamma)
            in  add (b :: bs', Gamma <+> [b], ps)
            end
  in  add ([], Gamma, ps)
  end
fun elabd (d : baredef, context, Gamma) =
  let fun toplevel what =
        case context
          of TOPLEVEL => id
           | _ => raise TypeError (what ^ " cannot appear " ^ contextString
                                                                        context)
      (* <new definition of [[mtypeof]]>=             *)
      fun mtypeof ((m, path), Gamma) =
        let fun ty (MPATH p) = strengthen (findModule (p, Gamma), txpath (p,
                                                                         Gamma))
                                   (* YYY only use of txpath --- move it? *)
              | ty (MPATHSEALED (mtx, p)) = sealed (mtx, ty (MPATH p))
              | ty (MUNSEALED defs)       = principal defs
              | ty (MSEALED (mtx, defs))  = sealed (mtx, principal defs)
            and sealed (mtx, mt') =
                  let val mt = elabmt ((mtx, path), Gamma)
                  in  case implements (path, mt', mt)
                        of OK () => mt
                         | ERROR msg => raise TypeError msg
                  end
            and principal ds = MTEXPORTS (elabdefs (ds, INMODULE path, Gamma))
            and elabdefs ([],    c, Gamma) = [] : (name * component) list
              | elabdefs ((loc, d) :: ds, c, Gamma) =
                  let val bindings = atLoc loc elabd (d, c, Gamma)
                      val comps'   = List.mapPartial asComponent bindings
                      val Gamma'   = Gamma <+> bindings
                      val comps''  = elabdefs (ds, c, Gamma')
                      (* <definition of [[asUnique]]>=                *)
                      fun asUnique following (x, c : component) =
                        let val c' = find (x, following)
                        in  case (c, c')
                              of (COMPVAL _, COMPVAL _) => NONE
                                                    (* repeated values are OK *)
                               | _ => raise TypeError ("Redefinition of " ^
                                                          whatcomp c ^ " " ^ x ^
                                                       " in module " ^
                                                                pathString path)
                        end handle NotFound _ => SOME (x, c)        
                  in  List.mapPartial (asUnique comps'') comps' @ comps''
                  end
        in  ty m
        end
      (* <boxed values 143>=                          *)
      val _ = op elabd : baredef * context * binding env -> (name * binding)
                                                                            list
      (* <boxed values 143>=                          *)
      type value_printer = value_printer
      val _ = op mtypeof : moddef rooted * binding env -> modty
      (* WILL WANT TO ADD A CONTEXT TO IDENTIFY THE MODULE TO *)
      (* [[subtypeError]].                            *)

  in  case d
        of EXP e => toplevel ("an expression (like " ^ expString e ^ ")")
                    (elabd (VAL ("it", e), context, Gamma))
         | MODULETYPE (T, mtx) =>
             let val mt = elabmt ((mtx, PNAME (MODTYPLACEHOLDER T)), Gamma)
             in  toplevel ("a module type (like " ^ T ^ ")")
                 [(T, ENVMODTY mt)]
             end
         | MODULE (name, mx) =>
             let val root = contextDot (context, name)
                 val mt   = mtypeof ((mx, root), Gamma)
             in  [(name, ENVMOD (mt, root))]
             end
         | GMODULE (f, formals, body) =>
             let val () = toplevel ("a generic module (like " ^ f ^ ")") ()
                 val fpath     = contextDot (context, f)
                 val idformals = map (fn (x, mtx) => (genmodident x, (x, mtx)))
                                                                         formals
                 val resultpath = PAPPLY (fpath, map (PNAME o fst) idformals)

                 fun addarg arg (args, res) = (arg :: args, res)

                 fun arrowtype ((mid : modident, (x, mtx)) :: rest, Gamma) =
                       let val mt = elabmt ((mtx, PNAME mid), Gamma)
                           val Gamma' = bind (x, ENVMOD (mt, PNAME mid), Gamma)
                       in  addarg (mid, mt) (arrowtype (rest, Gamma'))
                       end
                   | arrowtype ([], Gamma) = ([], mtypeof ((body, resultpath),
                                                                         Gamma))
                 val mt = MTARROW (arrowtype (idformals, Gamma))
             in  [(f, ENVMOD (mt, fpath))]
             end       
         | QNAME px => toplevel ("a qualified name (like " ^ pathexString px ^
                                                                            ")")
                       (elabd (EXP (VAR px), context, Gamma))
         | DEFINE (name, tau, lambda as (formals, body)) =>
             let val funty = FUNTY (map (fn (n, ty) => ty) formals, tau)
             in  elabd (VALREC (name, funty, LAMBDA lambda), context, Gamma)
             end
         | VAL (x, e) =>
             let val tau = typeof (e, Gamma)
             in  [(x, ENVVAL tau)]
             end
         | VALREC (f, tau, e as LAMBDA _) =>
             let val tau    = elabty (tau, Gamma)
                 val Gamma' = bind (f, ENVVAL tau, Gamma)
                 val tau'   = typeof (e, Gamma')
             in  if not (eqType (tau, tau')) then
                   raise TypeError ("identifier " ^ f ^
                                    " is declared to have type " ^
                                    typeString tau ^ " but has actual type " ^
                                    typeString tau')
                 else
                   [(f, ENVVAL tau)]
             end
         | VALREC (name, tau, _) =>
             raise TypeError ("(val-rec [" ^ name ^ " : " ^ tyexString tau ^
                              "] ...) must use (lambda ...) on right-hand side")
         | TYPE (t, tx) =>
             let val tau = elabty (tx, Gamma)
             in  [(t, ENVMANTY tau)]
             end
         | DATA dd => elabDataDef (dd, context, Gamma)
         | OVERLOAD ovl => overloadBindings (ovl, Gamma)
  end


(*****************************************************************)
(*                                                               *)
(*   EVALUATION, TESTING, AND THE READ-EVAL-PRINT LOOP FOR \MCL  *)
(*                                                               *)
(*****************************************************************)

(* Evaluation                                   *)
(*                                              *)
(* The components of the evaluator and read-eval-print *)
(* loop are organized as follows:               *)
(* <evaluation, testing, and the read-eval-print loop for \mcl>= *)
(* <definition of [[namedValueString]] for functional bridge languages>= *)
fun namedValueString x v =
  case v of CLOSURE _ => x
          | PRIMITIVE _ => x
          | _ => valueString v
(* The string returned by [[evaldef]] is the value, *)
(* unless the value is a named procedure, in which case *)
(* it is the name.                              *)
(* <boxed values 61>=                           *)
val _ = op namedValueString : name -> value -> string
(* <definition of [[namedValueString]] for functional bridge languages>= *)
fun namedValueString x v =
  case v of CLOSURE ((_, MODEXP _), _) => "generic module " ^ x
          | CLOSURE _ => x
          | PRIMITIVE _ => x
          | MODVAL _ => "module " ^ x
          | _ => valueString v
(* The string returned by [[evaldef]] is the value, *)
(* unless the value is a named procedure, in which case *)
(* it is the name.                              *)
(* <boxed values 179>=                          *)
val _ = op namedValueString : name -> value -> string
fun basename (PDOT (_, x)) = PNAME x
  | basename (PNAME x) = PNAME x
  | basename (instance as PAPPLY _) = instance
(* <definitions of [[matchRef]] and [[Doesn'tMatch]] ((elided))>= *)
exception Doesn'tMatch    (* pattern-match failure *)

fun matchRef (CONPAT (k, ps), CONVAL (k', vs)) =
     if basename k = k' then
       disjointUnion (ListPair.mapEq matchConval (ps, vs))
     else
       raise Doesn'tMatch
  | matchRef (CONPAT _, _) = raise Doesn'tMatch
  | matchRef (WILDCARD, _) = emptyEnv
  | matchRef (PVAR x,   v) = bind (x, ref v, emptyEnv)
and matchConval (PVAR x, vref) = bind (x, vref, emptyEnv)
  | matchConval (p, ref v) = matchRef (p, v)
(* Evaluating paths                             *)
(*                                              *)
(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
val nullsrc : srcloc = ("translated name in LETRECX", ~1)

fun evalpath (p : pathex, rho) =
  let fun findpath (PNAME (srcloc, x)) = !(find (x, rho))
        | findpath (PDOT (p, x)) =
            (case findpath p
               of MODVAL comps => (!(find (x, comps))
                                   handle NotFound x =>
                                     raise BugInTypeChecking "missing component"
                                                                               )
                | _ => raise BugInTypeChecking "selection from non-module")
        | findpath (PAPPLY (f, args)) = apply (findpath f, map findpath args)
  in  findpath p
  end
and apply (PRIMITIVE prim, vs) = prim vs
  | apply (CLOSURE ((formals, body), rho_c), vs) = 
      (eval (body, bindList (formals, map ref vs, rho_c))
       handle BindListLength => 
         raise BugInTypeChecking ("Wrong number of arguments to closure; " ^
                                  "expected (" ^ spaceSep formals ^ ")"))
  | apply _ = raise BugInTypeChecking "applied non-function"
(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and eval (e, rho : value ref env) =
  let val go = applyCheckingOverflow id in go end (* OMIT *)
  let fun ev (LITERAL n) = n
        (* Code for variables is just as in Chapter [->]. *)
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (VAR p) = evalpath (p, rho)
        | ev (SET (n, e)) = 
            let val v = ev e
            in  find (n, rho) := v;
                unitVal
            end
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (VCONX c) = evalpath (addloc ("bogus", ~33) c, rho)
        | ev (CASE (LITERAL v, (p, e) :: choices)) =
            (let val rho' = matchRef (p, v)
             in  eval (e, extend (rho, rho'))
             end
             handle Doesn'tMatch => ev (CASE (LITERAL v, choices)))
        | ev (CASE (LITERAL v, [])) =
            raise RuntimeError ("'case' does not match " ^ valueString v)
        | ev (CASE (e, choices)) =
            ev (CASE (LITERAL (ev e), choices))
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (IFX (e1, e2, e3)) = ev (if bool (ev e1) then e2 else e3)
        | ev (WHILEX (guard, body)) = 
            if bool (ev guard) then 
              (ev body; ev (WHILEX (guard, body)))
            else
              unitVal
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, unitVal)
            end
        (* Code for a [[lambda]] removes the types from the *)
        (* abstract syntax.                             *)
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (LAMBDA (args, body)) = CLOSURE ((map (fn (x, ty) => x) args, body)
                                                                          , rho)
        (* Code for application is almost as in Chapter [->], *)
        (* except if the program tries to apply a non-function, *)
        (* we raise [[BugInTypeChecking]], not [[RuntimeError]], *)
        (* because the type checker should reject any program *)
        (* that could apply a non-function.             *)

        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (APPLY (f, args, ref i))  =
           let val fv =
                 if i < 0 then
                   ev f
                 else
                   case ev f
                     of ARRAY a =>
                          (Array.sub (a, i)
                           handle Subscript => raise BugInTypeChecking
                                                             "overloaded index")
                      | _ => raise BugInTypeChecking
                                                  "overloaded name is not array"
           in  case fv
                 of PRIMITIVE prim => prim (map ev args)
                  | CLOSURE clo =>
                        (* Applying a closure is more interesting. To apply a *)

                          (* micro-Scheme closure correctly, I have to create *)

                          (* fresh locations to hold the values of the actual *)

                     (* parameters. In C, I use function [[allocate]]; in ML, *)

                        (* the built-in function [[ref]] does the same thing: *)

                         (* create a new location and initialize its contents *)

                           (* with a value. The ML expression \monoboxmap ref *)

                      (* actuals does half the work of C's [[bindalloclist]]; *)

                        (* function [[bindList]] does the other half. \mdbuse *)

                              (* schemebindalloclist                          *)

                         (* <apply closure [[clo]] to [[args]] ((mlscheme))>= *)
                                   let val ((formals, body), savedrho) = clo
                                       val actuals = map ev args
                                   in  eval (body, bindList (formals, map ref
                                                             actuals, savedrho))
                                       handle BindListLength => 
                                           raise RuntimeError (
                                      "Wrong number of arguments to closure; " ^
                                                               "expected (" ^
                                                         spaceSep formals ^ ")")
                                   end
                  | v => raise BugInTypeChecking "applied non-function"
           end
        (* Code for the [[LETX]] family is as in Chapter [->]. *)
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (LETX (LET, bs, body)) =
            let val (names, values) = ListPair.unzip bs
            in  eval (body, bindList (names, map (ref o ev) values, rho))
            end
        | ev (LETX (LETSTAR, bs, body)) =
            let fun step ((x, e), rho) = bind (x, ref (eval (e, rho)), rho)
            in  eval (body, foldl step rho bs)
            end
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (LETRECX (bs, body)) =
            let val (lhss, values) = ListPair.unzip bs
                val names = map fst lhss
                val _ = errorIfDups ("bound name", names, "letrec")
                fun unspecified () = NUM 42
                val rho' = bindList (names, map (fn _ => ref (unspecified()))
                                                                    values, rho)
                val updates = map (fn (x, e) => (x, eval (e, rho'))) bs
            in  List.app (fn ((x, _), v) => find (x, rho') := v) updates; 
                eval (body, rho')
            end
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (MODEXP components) =
            let fun step ((x, e), (results', rho)) =
                  let val loc = ref (eval (e, rho))
                  in  ((x, loc) :: results', bind (x, loc, rho))
                  end
                val (results', _) = foldl step ([], rho) components
            in  MODVAL results'
            end
        (* <more alternatives for [[ev]] for {\mcl}>=   *)
        | ev (ERRORX es) =
            raise RuntimeError (spaceSep (map (valueString o ev) es))
        | ev (EXP_AT (loc, e)) = atLoc loc ev e
(* Evaluating expressions                       *)
(*                                              *)
(* The implementation of the evaluator is almost *)
(* identical to the implementation in Chapter [->]. *)
(* There are only two significant differences: we have *)
(* to deal with the mismatch in representations between *)
(* the abstract syntax [[LAMBDA]] and the value *)
(* [[CLOSURE]], and we have to write cases for the *)
(* [[TYAPPLY]] and [[TYLAMBDA]] expressions. Another *)
(* difference is that many potential run-time errors *)
(* should be impossible because the relevant code would *)
(* be rejected by the type checker. If one of those *)
(* errors occurs anyway, we raise the exception *)
(* [[BugInTypeChecking]], not [[RuntimeError]]. \ *)
(* mclflabeleval                                *)
(* <boxed values 177>=                          *)
val _ = op eval : exp * value ref env -> value
val _ = op ev   : exp                 -> value
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

  in  ev e
  end
(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and defbindings (VAL (x, e), rho) =
      [(x, ref (eval (e, rho)))]
  | defbindings (VALREC (x, tau, e), rho) =
      let val this = ref (SYM "placedholder for val rec")
(* Evaluating a definition can produce a new    *)
(* environment. The function [[evaldef]] also returns a *)
(* string which, if nonempty, should be printed to show *)
(* the value of the item. Type soundness requires a *)
(* change in the evaluation rule for [[VAL]]; as *)
(* described in Exercise [->] in Chapter [->], [[VAL]] *)
(* must always create a new binding. \mclflabelevaldef  *)
(* [*]                                          *)
(* <boxed values 178>=                          *)
val _ = op defbindings : baredef * value ref env -> (name * value ref) list
          val rho' = bind (x, this, rho)
          val v    = eval (e, rho')
          val _    = this := v
      in  [(x, this)]
      end
  | defbindings (EXP e, rho) = 
      defbindings (VAL ("it", e), rho)
  | defbindings (QNAME _, rho) = 
      []
  | defbindings (DEFINE (f, tau, lambda), rho) =
      defbindings (VALREC (f, tau, LAMBDA lambda), rho)
(* In the [[VALREC]] case, the interpreter evaluates  *)
(* [[e]] while [[name]] is still bound to [[NIL]]---that *)
(* is, before the assignment to [[find (name, rho)]]. *)
(* Therefore, as in Typed uScheme, evaluating [[e]] must *)
(* not evaluate [[name]]---because the mutable cell for *)
(* [[name]] does not yet contain its correct value. *)

(* XXX I probably should evaluate a definition by using *)
(* [[defexps]] and [[eval]].                    *)
(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
  | defbindings (TYPE _, _) =
      []
  | defbindings (DATA (t, typed_vcons), rho) =
      let fun binding (K, tau) =
            let val v = case tau of FUNTY _ => PRIMITIVE (fn vs => CONVAL (PNAME
                                                                 K, map ref vs))
                                  | _ => CONVAL (PNAME K, [])
            in  (K, ref v)
            end
      in  map binding typed_vcons
      end
  | defbindings (MODULE (x, m), rho) =
      [(x, ref (evalmod (m, rho)))]
  | defbindings (GMODULE (f, formals, body), rho) =
      [(f, ref (CLOSURE ((map fst formals, modexp body), rho)))]
  | defbindings (MODULETYPE (a, _), rho) = 
      []

(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
  | defbindings (OVERLOAD ps, rho) = 
      let fun overload (p :: ps, rho) =
                let val x = plast p
                    val v = extendOverloadTable (x, evalpath (p, rho), rho)
                    val loc = ref (ARRAY v)
                in  (x, loc) :: overload (ps, bind (x, loc, rho))
                end
            | overload ([], rho) = []
      in  overload (ps, rho)
      end
(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and extendOverloadTable (x, v, rho) =
  let val currentVals =
        (case find (x, rho)
           of ref (ARRAY a) => a
            | _ => Array.fromList [])
        handle NotFound _ => Array.fromList []
  in  Array.tabulate (1 + Array.length currentVals,
                      fn 0 => v | i => Array.sub (currentVals, i - 1))
  end

(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and defexps (VAL (x, e)) = [(x, e)]
  | defexps (VALREC (x, tau, e)) = [(x, LETRECX ([((x, tau), e)], VAR (PNAME (
                                                                 nullsrc, x))))]
  | defexps (EXP e) =  [("it", e)]
  | defexps (QNAME _) = []
  | defexps (DEFINE (f, tau, lambda)) = defexps (VALREC (f, tau, LAMBDA lambda))
  | defexps (TYPE _) = []
  | defexps (DATA (t, typed_vcons)) = 
      let fun isfuntype (FUNTY _)         = true
            | isfuntype _                 = false
          fun vconExp (K, t) =
            let val v = if isfuntype t then
                          PRIMITIVE (fn vs => CONVAL (PNAME K, map ref vs))
                        else
                          CONVAL (PNAME K, [])
            in  (K, LITERAL v)
            end
      in  map vconExp typed_vcons
      end
  | defexps (MODULE (x, m)) = [(x, modexp m)]
  | defexps (GMODULE (f, formals, body)) =
      [(f, LAMBDA (map (fn (x, _) => (x, ANYTYPE)) formals, modexp body))]
  | defexps (MODULETYPE (a, _)) = []
  | defexps (OVERLOAD ovls) = unimp "overloadiang within generic module"

(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and modexp (MPATH px)            = VAR px
  | modexp (MPATHSEALED (_, px)) = VAR px
  | modexp (MSEALED (_, defs))   = MODEXP ((List.concat o map (located defexps))
                                                                           defs)
  | modexp (MUNSEALED defs)      = MODEXP ((List.concat o map (located defexps))
                                                                           defs)


(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and evalmod (MSEALED (_, ds), rho) = evalmod (MUNSEALED ds, rho)
  | evalmod (MPATH p, rho) = evalpath (p, rho)
  | evalmod (MPATHSEALED (mtx, p), rho) = evalpath (p, rho)
  | evalmod (MUNSEALED defs, rho) = MODVAL (rev (defsbindings (defs, rho)))

               (* XXX type checker should ensure there are no duplicates here *)
(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and defsbindings ([],   rho) = []
  | defsbindings (d::ds, rho) =
      let val bs   = leftLocated defbindings (d, rho)
          val rho' = foldl (fn ((x, loc), rho) => bind (x, loc, rho)) rho bs
      in  bs @ defsbindings (ds, rho')
      end
(* <definitions of [[eval]] and [[evaldef]] for {\mcl}>= *)
and evaldef (d, rho) =
  let fun single [(_, loc)] = ! loc
        | single _        = raise InternalError
                                             "wrong number of bindings from def"
(* <boxed values 180>=                          *)
val _ = op evaldef : baredef * value ref env -> value ref env * value list
      val bindings = defbindings (d, rho)
      
      fun string (VAL (x, e))         = namedValueString x (single bindings)
        | string (VALREC (x, tau, e)) = namedValueString x (single bindings)
        | string (EXP _)              = valueString (single bindings)
        | string (QNAME px)           = raise InternalError
                                                          "NAME reached evaldef"
        | string (DEFINE (f, _, _))   = namedValueString f (single bindings)
        | string (TYPE (t, tau))      = "type " ^ t
        | string (DATA _) = unimp "DATA definitions"
        | string (GMODULE (f, _, _))= namedValueString f (single bindings)
        | string (MODULE (x, m))      = namedValueString x (single bindings)
        | string (MODULETYPE (a, _))  = "module type " ^ a
        | string (OVERLOAD ps)        = "overloaded names " ^ separate("", " ")
                                                                  (map plast ps)

      val rho' = foldl (fn ((x, loc), rho) => bind (x, loc, rho)) rho bindings
  in  (rho', map (! o snd) bindings)   (* 2nd component was (string d) *)
  end
(* <definitions of [[basis]] and [[processDef]] for \mcl>= *)
fun processOverloading (ps, (Gamma, rho), interactivity) =
  let fun next (p, (Gamma, rho)) =
        let val (tau, first) =
              case pathfind (p, Gamma)
                of ENVVAL tau => (tau, okOrTypeError (firstArgType (pathexString
                                                                       p, tau)))
                 | c => (* <can't overload a [[c]]>=                    *)
                        raise TypeError (
                    "only functions can be overloaded, but " ^ whatdec c ^ " " ^
                                         pathexString p ^ " is not a function")
            val x = plast p

            val currentTypes =
              (case find (x, Gamma)
                 of ENVOVLN vals => vals
                  | _ => []) handle NotFound _ => []
            val newTypes = tau :: currentTypes
            val Gamma' = bind (x, ENVOVLN newTypes, Gamma)

            (************
            val currentVals =
              if null currentTypes then Array.fromList []
              else case find (x, rho)
                     of ref (ARRAY a) => a
                      | _ => raise BugInTypeChecking
                                                  "overloaded name is not ARRAY"
            val v = evalpath (p, rho)
            val newVals = Array.tabulate (1 + Array.length currentVals,
                                          fn 0 => v | i => Array.sub (
                                                            currentVals, i - 1))
            *****)
            val newVals = extendOverloadTable (x, evalpath (p, rho), rho)
            val rho' = bind (x, ref (ARRAY newVals), rho)

            val _ = if prints interactivity then
                      app print ["overloaded ", x, " : ", typeString tau, "\n"]
                    else
                      ()
        in  (Gamma', rho')
        end
  in  foldl next (Gamma, rho) ps
  end

(* <definitions of [[basis]] and [[processDef]] for \mcl>= *)
type basis = binding env * value ref env
fun defmarker (MODULETYPE _) = " = "
  | defmarker (DATA _)       = ""
  | defmarker _              = " : "

fun processDef ((loc, DATA dd), (Gamma, rho), interactivity) =
      atLoc loc processDataDef (dd, (Gamma, rho), interactivity)
  | processDef ((loc, QNAME px), (Gamma, rho), interactivity) =
      let val c = pathfind (px, Gamma)
          val x = pathexString px
          val respond = println o concat
          fun typeResponse ty = if x = ty then ["abstract type ", x]
                                else ["type ", x, " = ", ty]
          fun response (ENVVAL _) = raise InternalError
                                                       "ENVVAL reached response"
            | response (ENVMANTY tau)                = typeResponse(typeString
                                                                            tau)
            | response (ENVMOD (mt as MTARROW _, _)) = ["generic module ", x,
                                                             " : ", mtString mt]
            | response (ENVMOD (mt, _))              = ["module ", x, " : ",
                                                                    mtString mt]
            | response (ENVMODTY mt)                 = ["module type ", x, " = "
                                                                  , mtString mt]
            | response (ENVOVLN []) = raise InternalError
                                                         "empty overloaded name"
            | response (ENVOVLN (tau :: taus)) =
                "overloaded " :: x :: " : " :: typeString tau ::
                map (fn t => "\n           " ^ x ^ " : " ^ typeString t) taus
                  
      val _ = if prints interactivity then
                case c
                  of ENVVAL _ =>
                       ignore (processDef ((loc, EXP (VAR px)), (Gamma, rho),
                                                                 interactivity))
                   | _ =>
                       respond (response c)
              else
                ()
      in  (Gamma, rho)
      end
  | processDef ((loc, OVERLOAD ps), (Gamma, rho), interactivity) =
      atLoc loc processOverloading (ps, (Gamma, rho), interactivity)
  | processDef ((loc, d), (Gamma, rho), interactivity) =

    (* (app (fn (x, c) => app print [x, " is ", whatcomp c, "\n"]) Gamma; id) *)
      let val bindings   = atLoc loc elabd (d, TOPLEVEL, Gamma)
          val Gamma      = Gamma <+> bindings
          val printer    = defPrinter (d, Gamma)
          val (rho, vs)  = atLoc loc evaldef (d, rho)
          
          fun callPrintExp i v =
            APPLY (VAR (PNAME (loc, "print")), [LITERAL v], ref i)

          fun printfun x tau v =
            let val resolved = (case find ("print", Gamma)
                                  of ENVOVLN taus => resolveOverloaded ("print",
                                                                      tau, taus)
                                   | _ => ERROR "no printer for tau")
                               handle NotFound _ => ERROR "'print' not found"
            in  case resolved
                  of OK (_, i) => ignore (eval (callPrintExp i v, rho))
                   | ERROR _ =>
                       case d
                         of EXP _ => print (valueString v)
                          | _ => case tau
                                   of FUNTY _ => print x
                                    | _       => print (valueString v)
            end

          val _ = if prints interactivity then
                    (printer printfun vs; print "\n")
                  else
                    ()
      in  (Gamma, rho)
      end
(* A literal is either a bare symbol like x, which is *)
(* satisfied by [[#t]], or it is a two-element list like *)
(* \monobox(not x), which is satisfied by [[#f]]. I can *)
(* avoid a case analysis by observing that in both *)
(* cases, the value that satisfies a literal [[lit]] is *)
(* equal to \monobox(symbol? lit).              *)
(* <boxed values 147>=                          *)
val _ = op processDef : def * basis * interactivity -> basis
fun dump_names (Gamma, rho) = app (println o fst) Gamma (*OMIT*)

(* <shared definition of [[withHandlers]]>=     *)
fun withHandlers f a caught =
  f a
  handle RuntimeError msg   => caught ("Run-time error <at loc>: " ^ msg)
       | NotFound x         => caught ("Name " ^ x ^ " not found <at loc>")
       | Located (loc, exn) =>
           withHandlers (fn _ => raise exn) a (fn s => caught (fillAtLoc (s, loc
                                                                             )))
       (* In addition to [[RuntimeError]], [[NotFound]], and *)
       (* [[Located]], [[withHandlers]] catches many exceptions *)
       (* that are predefined ML's Standard Basis Library. *)
       (* These exceptions signal things that can go wrong *)
       (* while evaluating an expression or when reading a *)
       (* file.                                        *)

(* <other handlers that catch non-fatal exceptions and pass messages to [[caught]]>= *)
       | Div                => caught ("Division by zero <at loc>")
       | Overflow           => caught ("Arithmetic overflow <at loc>")
       | Subscript          => caught ("Array index out of bounds <at loc>")
       | Size               => caught (
                                "Array length too large (or negative) <at loc>")
       | IO.Io { name, ...} => caught ("I/O error <at loc>: " ^ name)
       (* I reuse the same exception handlers in later *)
       (* interpreters.                                *)

       (* The read-eval-print loop                     *)
       (*                                              *)
       (* Typed Impcore reuses the read-eval-print loop defined *)
       (* in \crefpagemlscheme.repl. But Typed Impcore needs *)
       (* handlers for new exceptions: [[TypeError]] and *)
       (* [[BugInTypeChecking]]. [[TypeError]] is raised not at *)
       (* parsing time, and not at evaluation time, but at *)
       (* typechecking time. [[BugInTypeChecking]] should never *)
       (* be raised.                                   *)

(* <other handlers that catch non-fatal exceptions and pass messages to [[caught]] ((type-checking))>= *)
       | TypeError         msg => caught ("type error <at loc>: " ^ msg)
       | BugInTypeChecking msg => caught ("bug in type checking: " ^ msg)
(* Here is the promised [[failtest]].           *)
(* <shared unit-testing utilities>=             *)
fun failtest strings = (app eprint strings; eprint "\n"; false)
(* In each bridge language, test results are reported *)
(* the same way. If there are no tests, there is no *)
(* report. (The report's format is stolen from the *)
(* DrRacket programming environment.)           *)
(* <shared unit-testing utilities>=             *)
fun reportTestResultsOf what (npassed, nthings) =
  case (npassed, nthings)
    of (_, 0) => ()  (* no report *)
     | (0, 1) => println ("The only " ^ what ^ " failed.")
     | (1, 1) => println ("The only " ^ what ^ " passed.")
     | (0, 2) => println ("Both " ^ what ^ "s failed.")
     | (1, 2) => println ("One of two " ^ what ^ "s passed.")
     | (2, 2) => println ("Both " ^ what ^ "s passed.")
     | _ => if npassed = nthings then
               app print ["All ", intString nthings, " " ^ what ^ "s passed.\n"]
            else if npassed = 0 then
               app print ["All ", intString nthings, " " ^ what ^ "s failed.\n"]
            else
               app print [intString npassed, " of ", intString nthings,
                          " " ^ what ^ "s passed.\n"]
val reportTestResults = reportTestResultsOf "test"
(* <definition of [[testIsGood]] for {\mcl}>=   *)
fun comparisonIndex env tau =
  let val wanted = FUNTY ([tau, tau], booltype)
      val index  =
        case find ("=", env)
          of ENVOVLN taus =>
               (case resolveOverloaded ("=", tau, taus)
                  of OK (compty, i) =>
                       if eqType (compty, wanted) then OK i
                       else (ERROR o String.concat)
                            ["on type ", typeString tau,
                                                       " operation = has type ",
                             typeString compty]
                   | ERROR msg => ERROR msg)
           | _ => ERROR "operator = is not overloaded, so I can't check-expect"
  in  index
  end
(* <definition of [[testIsGood]] for {\mcl}>=   *)
fun noTypeError f x k =
  (f x; true) handle TypeError msg => failtest (k msg)

fun testIsGood (test, (E, rho)) =
  let fun ty e = typeof (e, E)
                 handle NotFound x => raise TypeError ("name " ^ x ^
                                                              " is not defined")

    (* <shared [[check{Expect,Assert,Error,Type}Checks]], which call [[ty]]>= *)
      fun checkTypeChecks (e, tau) =
        let val tau' = ty e
        in  true
        end
        handle TypeError msg => 
               failtest ["In (check-type ", expString e, " " ^ typeString tau,
                                                                     "), ", msg]

    (* <shared [[check{Expect,Assert,Error,Type}Checks]], which call [[ty]]>= *)
      fun checkExpectChecks (e1, e2) = 
        let val tau1 = ty e1
            val tau2 = ty e2
        in  if eqType (tau1, tau2) then
              true
            else
              raise TypeError ("Expressions have types " ^ typeString tau1 ^
                                  " and " ^ typeString tau2)
        end handle TypeError msg =>
        failtest ["In (check-expect ", expString e1, " ", expString e2, "), ",
                                                                            msg]

    (* <shared [[check{Expect,Assert,Error,Type}Checks]], which call [[ty]]>= *)
      fun checkOneExpChecks inWhat e =
        let val tau1 = ty e
        in  true
        end handle TypeError msg =>
        failtest ["In (", inWhat, " ", expString e, "), ", msg]
      val checkAssertChecks = checkOneExpChecks "check-assert"
      val checkErrorChecks  = checkOneExpChecks "check-error"
      fun checks (CHECK_EXPECT (e1, e2)) =
            checkExpectChecks (e1, e2) andalso
            (case comparisonIndex E (ty e1)
               of OK i => true
                | ERROR msg =>
                    failtest ["cannot check-expect ", expString e1, ": ", msg])
        | checks (CHECK_ASSERT e)        = checkAssertChecks e
        | checks (CHECK_ERROR  e)        = checkErrorChecks  e
        | checks (CHECK_TYPE (e, t))     =
            noTypeError elabty (t, E)
            (fn msg => ["In (check-type ", expString e, " " ^ tyexString t,
                                                                    "), ", msg])
        | checks (CHECK_TYPE_ERROR e)    = true
        | checks (CHECK_MTYPE (pathx, mt)) =
            let val path = elabpath (pathx, E)
                val _ = elabmt ((mt, path), E)
            in  true
            end handle TypeError msg =>
              failtest ["In (check-module-type ", pathexString pathx, " ",
                        mtxString mt, "), ", msg]

      fun deftystring d =
        let val comps = List.mapPartial asComponent (elabd (d, TOPLEVEL, E))
        in  if null comps then
              (case d of OVERLOAD _ => "an overloaded name" 
                       | GMODULE _ => "a generic module"   
                       | MODULETYPE _ => "a module type"
                       | _ => raise InternalError "unrecognized definition")
            else
              commaSep (map (whatcomp o snd) comps)
        end handle NotFound x => raise TypeError ("name " ^ x ^
                                                              " is not defined")


      fun outcome e = withHandlers (fn () => OK (eval (e, rho))) () (ERROR o
                                                                     stripAtLoc)
      (* <definition of [[asSyntacticValue]] for \mcl>= *)
      fun asSyntacticValue (LITERAL v) = SOME v
        | asSyntacticValue (VCONX c)   = SOME (CONVAL (c, []))
        | asSyntacticValue (APPLY (e, es, _)) =
            (case (asSyntacticValue e, optionList (map asSyntacticValue es))
               of (SOME (CONVAL (c, [])), SOME vs) => SOME (CONVAL (c, map ref
                                                                            vs))
                | _ => NONE)
        | asSyntacticValue _ = NONE
      (* <boxed values 195>=                          *)
      val _ = op asSyntacticValue : exp -> value option
      (* <shared [[whatWasExpected]]>=                *)
      fun whatWasExpected (e, outcome) =
        case asSyntacticValue e
          of SOME v => valueString v
           | NONE =>
               case outcome
                 of OK v => valueString v ^ " (from evaluating " ^ expString e ^
                                                                             ")"
                  | ERROR _ =>  "the result of evaluating " ^ expString e
      (* When a [[check-expect]] fails, function      *)
      (* [[whatWasExpected]] reports what was expected. If the *)
      (* thing expected was a syntactic value, I show just the *)
      (* value. Otherwise I show the syntax, plus whatever the *)
      (* syntax evaluated to. The definition of       *)
      (* [[asSyntacticValue]] is language-dependent.  *)
      (* <boxed values 205>=                          *)
      val _ = op whatWasExpected  : exp * value error -> string
      val _ = op asSyntacticValue : exp -> value option
      (* <shared [[checkExpectPassesWith]], which calls [[outcome]]>= *)
      val cxfailed = "check-expect failed: "
      fun checkExpectPassesWith equals (checkx, expectx) =
        case (outcome checkx, outcome expectx)
          of (OK check, OK expect) => 
               equals (check, expect) orelse
               failtest [cxfailed, " expected ", expString checkx,
                                                             " to evaluate to ",
                         whatWasExpected (expectx, OK expect), ", but it's ",
                         valueString check, "."]
           | (ERROR msg, tried) =>
               failtest [cxfailed, " expected ", expString checkx,
                                                             " to evaluate to ",
                         whatWasExpected (expectx, tried), ", but evaluating ",
                         expString checkx, " caused this error: ", msg]
           | (_, ERROR msg) =>
               failtest [cxfailed, " expected ", expString checkx,
                                                             " to evaluate to ",
                         whatWasExpected (expectx, ERROR msg),
                                                            ", but evaluating ",
                         expString expectx, " caused this error: ", msg]

(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
      (*                                              *)
      (*  {combinators} \theaderUnit-testing functions *)
      (*  provided by each language \combinatoroutcomeexp *)
      (*  -> value error \combinatortyexp -> ty error \ *)
      (*  combinatortestEqualvalue * value -> bool \  *)
      (*  combinatorvalueStringvalue -> string \combinator *)
      (*  expStringexp -> string \combinator          *)
      (*  testIsGoodunit_test list * basis -> bool \theader *)
      (*  Shared functions for unit testing \combinator *)
      (*  whatWasExpectedexp * value error -> string \ *)
      (*  combinatorcheckExpectPassesexp * exp -> bool \ *)
      (*  combinatorcheckErrorPassesexp -> bool \combinator *)
      (*  numberOfGoodTestsunit_test list * basis -> int \ *)
      (*  combinatorprocessTestsunit_test list * basis -> *)
      (*  unit {combinators}                          *)
      (*                                              *)
      (* Unit-testing functions                       *)

(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
      (*                                              *)
      (* Function [[checkExpectPasses]] runs a        *)
      (* [[check-expect]] test and tells if the test passes. *)
      (* If the test does not pass, [[checkExpectPasses]] also *)
      (* writes an error message. Error messages are written *)
      (* using [[failtest]], which, after writing the error *)
      (* message, indicates failure by returning [[false]]. *)
      (* <boxed values 206>=                          *)
      val _ = op checkExpectPassesWith : (value * value -> bool) -> exp * exp ->
                                                                            bool
      val _ = op outcome  : exp -> value error
      val _ = op failtest : string list -> bool

(* <shared [[checkAssertPasses]] and [[checkErrorPasses]], which call [[outcome]]>= *)
      val cafailed = "check-assert failed: "
      fun checkAssertPasses checkx =
            case outcome checkx
              of OK check => bool check orelse
                             failtest [cafailed, " expected assertion ",
                                                               expString checkx,
                                       " to hold, but it doesn't"]
               | ERROR msg =>
                   failtest [cafailed, " expected assertion ", expString checkx,
                             " to hold, but evaluating it caused this error: ",
                                                                            msg]
      (* Function [[checkAssertPasses]] does the analogous job *)
      (* for [[check-assert]].                        *)
      (* <boxed values 207>=                          *)
      val _ = op checkAssertPasses : exp -> bool

(* <shared [[checkAssertPasses]] and [[checkErrorPasses]], which call [[outcome]]>= *)
      val cefailed = "check-error failed: "
      fun checkErrorPasses checkx =
            case outcome checkx
              of ERROR _ => true
               | OK check =>
                   failtest [cefailed, " expected evaluating ", expString checkx
                                                                               ,
                             " to cause an error, but evaluation produced ",
                             valueString check]
      (* Function [[checkErrorPasses]] does the analogous job *)
      (* for [[check-error]].                         *)
      (* <boxed values 208>=                          *)
      val _ = op checkErrorPasses : exp -> bool

      fun checkExpectPasses (c, e) =
        let val i = case comparisonIndex E (ty c)
                      of OK i => i
                       | ERROR _ => raise InternalError
                                                  "overloaded = in check-expect"
            val eqfun =
              case !(find ("=", rho))
                of ARRAY vs => (Array.sub (vs, i)
                                handle _ => raise InternalError
                                                         "overloaded subscript")
                 | _ => raise InternalError "overloaded = not array"
                     
            fun testEqual (v1, v2) =
              case eval (APPLY (LITERAL eqfun, [LITERAL v1, LITERAL v2], ref
                                                       notOverloadedIndex), rho)
                of CONVAL (PNAME "#t", []) => true
                 | _ => false

        in  checkExpectPassesWith testEqual (c, e)
        end

      fun checkMtypePasses (pathx, mtx) =
        let val path = txpath (pathx, E)
            val principal = strengthen (findModule (pathx, E), path)
            val mt = elabmt ((mtx, path), E)
        in  case implements (path, principal, mt)
              of OK () => true
               | ERROR msg => raise TypeError msg
        end handle TypeError msg =>
          failtest ["In (check-module-type ", pathexString pathx, " ",
                    mtxString mtx, "), ", msg]


(* <shared [[checkTypePasses]] and [[checkTypeErrorPasses]], which call [[ty]]>= *)
      fun checkTypePasses (e, tau) =
        let val tau' = ty e
        in  if eqType (tau, tau') then
              true
            else
              failtest ["check-type failed: expected ", expString e,
                                                               " to have type ",
                     typeString tau, ", but it has type ", typeString tau']
        end handle TypeError msg =>
            failtest ["In (check-type ", expString e, " " ^ typeString tau,
                                                                     "), ", msg]

(* <shared [[checkTypePasses]] and [[checkTypeErrorPasses]], which call [[ty]]>= *)
      fun checkTypeErrorPasses (EXP e) =
            (let val tau = ty e
             in  failtest ["check-type-error failed: expected ", expString e,
                       " not to have a type, but it has type ", typeString tau]
             end handle TypeError msg => true
                      | Located (_, TypeError _) => true)
        | checkTypeErrorPasses d =
            (let val t = deftystring d
             in  failtest ["check-type-error failed: expected ", defString d,

                         " to cause a type error, but it successfully defined ",
                           defName d, " : ", t
                          ] 
             end handle TypeError msg => true
                      | Located (_, TypeError _) => true)
      fun passes (CHECK_EXPECT (c, e)) = checkExpectPasses (c, e)
        | passes (CHECK_ASSERT c)      = checkAssertPasses c
        | passes (CHECK_ERROR c)       = checkErrorPasses  c
        | passes (CHECK_TYPE (c, t))   = checkTypePasses   (c, elabty (t, E))
        | passes (CHECK_TYPE_ERROR (loc, c))  = atLoc loc checkTypeErrorPasses c
        | passes (CHECK_MTYPE c)       = checkMtypePasses c

  in  checks test andalso passes test
  end
fun assertPtype (x, t, basis) = unimp "assertPtype"

(* <shared definition of [[processTests]]>=     *)
fun numberOfGoodTests (tests, rho) =
  foldr (fn (t, n) => if testIsGood (t, rho) then n + 1 else n) 0 tests
fun processTests (tests, rho) =
      reportTestResults (numberOfGoodTests (tests, rho), length tests)
(* <boxed values 209>=                          *)
val _ = op processTests : unit_test list * basis -> unit
(* <shared read-eval-print loop and [[processPredefined]]>= *)
fun processPredefined (def,basis) = 
  processDef (def, basis, noninteractive)
(* When reading definitions of predefined functions, *)
(* there's no interactivity.                    *)
(* <boxed values 22>=                           *)
val _ = op noninteractive    : interactivity
val _ = op processPredefined : def * basis -> basis
(* <shared read-eval-print loop and [[processPredefined]]>= *)
fun readEvalPrintWith errmsg (xdefs, basis, interactivity) =
  let val unitTests = ref []

(* <definition of [[processXDef]], which can modify [[unitTests]] and call [[errmsg]]>= *)
      fun processXDef (xd, basis) =
        let (* Let's see the generic code that ``processes'' an *)
            (* extended definition. To process a [[USE]] form, *)
            (* we call function [[useFile]], which reads definitions *)
            (* from a file and recursively passes them to   *)
            (* [[readEvalPrintWith]].                       *)
            (* <definition of [[useFile]], to read from a file>= *)
            fun useFile filename =
              let val fd = TextIO.openIn filename
                  val (_, printing) = interactivity
                  val inter' = (NOT_PROMPTING, printing)
              in  readEvalPrintWith errmsg (filexdefs (filename, fd, noPrompts),
                                                                  basis, inter')
                  before TextIO.closeIn fd
              end
            fun try (USE filename) = useFile filename
              | try (TEST t)       = (unitTests := t :: !unitTests; basis)
              | try (DEF def)      = processDef (def, basis, interactivity)
              | try (DEFS ds)      = foldl processXDef basis (map DEF ds)
                                                                        (*OMIT*)
            fun caught msg = (errmsg (stripAtLoc msg); basis)
            val _ = resetOverflowCheck ()     (* OMIT *)
        in  withHandlers try xd caught
        end 
      (* The extended-definition forms [[USE]] and [[TEST]] *)
      (* are implemented in exactly the same way for every *)
      (* language: internal function [[try]] passes each *)
      (* [[USE]] to [[useFile]], and it adds each [[TEST]] to *)
      (* the mutable list [[unitTests]]---just as in the *)
      (* C code in \secrefpageimpcore.readevalprint. Function *)
      (* [[try]] passes each true definition [[DEF]] to *)
      (* function [[processDef]], which does the      *)
      (* language-dependent work.                     *)
      (* <boxed values 25>=                           *)
      val _ = op errmsg     : string -> unit
      val _ = op processDef : def * basis * interactivity -> basis
      val basis = streamFold processXDef basis xdefs
      val _     = processTests (!unitTests, basis)
(* <boxed values 24>=                           *)
val _ = op readEvalPrintWith : (string -> unit) ->                     xdef
                                         stream * basis * interactivity -> basis
val _ = op processXDef       : xdef * basis -> basis
  in  basis
  end
(* Function [[readEvalPrintWith]] executes essentially *)
(* the same imperative actions as the C function *)
(* [[readevalprint]] (\chunkref                 *)
(* scheme.chunk.readevalprint): allocate space for a *)
(* list of pending unit tests; loop through a stream of *)
(* extended definitions, using each one to update the *)
(* environment(s); and process the pending unit tests. *)
(* (The looping action in the ML code is implemented by *)
(* function [[streamFold]], which applies       *)
(* [[processXDef]] to every element of [[xdefs]]. *)
(* Function [[streamFold]] is the stream analog of the *)
(* list function [[foldl]].) Unlike the C       *)
(* [[readevalprint]], which updates the environment *)
(* in place by writing through a pointer, the   *)
(* ML function ends by returning the updated environment *)
(* (s).                                         *)




(*****************************************************************)
(*                                                               *)
(*   IMPLEMENTATIONS OF \MCL\ PRIMITIVES AND DEFINITION OF [[INITIALBASIS]] *)
(*                                                               *)
(*****************************************************************)

(* <implementations of \mcl\ primitives and definition of [[initialBasis]]>= *)
val intmodenv    = foldl (addValWith (ref o PRIMITIVE)) emptyEnv intPrims
val arraymodenv  = foldl (addValWith (ref o PRIMITIVE)) emptyEnv arrayPrims
val boolmodenv   = foldl (addValWith (ref o PRIMITIVE)) emptyEnv boolPrims
val unitmodenv = bind ("unit", ref (CONVAL (PNAME "unit", [])), emptyEnv)
val symmodenv  = foldl (addValWith (ref o PRIMITIVE)) emptyEnv symPrims

val modules = 
  [ ("Int",  intmod,  MODVAL intmodenv)
  , ("Bool", boolmod, MODVAL boolmodenv)
  , ("Unit", unitmod, MODVAL unitmodenv)
  , ("Sym",  symmod,  MODVAL symmodenv)
  , (arraymodname,  arraymod,
     CLOSURE ((["Elem"], MODEXP (map (fn (x, f, _) => (x, LITERAL (PRIMITIVE f))
                                                                 ) arrayPrims)),
              emptyEnv))
  , ("UnsafeArray",  uarraymod,
     CLOSURE ((["Elem"], MODEXP (map (fn (x, f, _) => (x, LITERAL (PRIMITIVE f))
                                                                ) uarrayPrims)),
              emptyEnv))
  , ("ArrayCore",  arraymod,
     CLOSURE ((["Elem"], MODEXP (map (fn (x, f, _) => (x, LITERAL (PRIMITIVE f))
                                                                 ) arrayPrims)),
              emptyEnv))

  , ("#t", ENVVAL booltype, CONVAL (PNAME "#t", []))
  , ("#f", ENVVAL booltype, CONVAL (PNAME "#f", []))
  ]

fun addmod ((x, dbl, v), (Gamma, rho)) =
  (bind (x, dbl, Gamma), bind (x, ref v, rho))

val initialRho = bind (overloadTable, ref (ARRAY emptyOverloadTable), emptyEnv)

val initialBasis = foldl addmod (emptyEnv, initialRho) modules : basis

val initialBasis =
  let val predefinedTypes = 
                             [
                              ";  Qualified names                              "
                             ,
                              ";                                               "
                             ,
                     ";  Here are some examples of qualified names: {indented} "
                             ,
                              ";                                               "
                             ,
                              ";  Name              Component                  "
                             ,
                        ";  [[IntArray.t]]    The type of an array of integers "
                             ,
                          ";  [[IntArray.size]] Function giving the size of an "
                             ,
                              ";                 array of integers             "
                             ,
                       ";  [[IntArray.new]]  Function that creates a new array "
                             ,
                              ";                 of integers                   "
                             ,
                              ";  [[Int.t]]         The type of an integer     "
                             ,
                              ";  [[Int.+]]         Integer addition           "
                             ,
                              ";  [[Bool.t]]        The type of a Boolean      "
                             ,
                              ";                                               "
                             ,
                              ";  {indented} To write general cases using      "
                             ,
                     ";  metavariables, I typically use M for a module name, x "
                             ,
                            ";   for a value name, and t for a type name. So a "
                             ,
                          ";  general value component might be M.x, and a type "
                             ,
                      ";  component might be M.t. \\notationM.xvalue component "
                             ,
                       ";  of a module \\notationM.ttype component of a module "
                             ,
                              ";                                               "
                             ,
                           ";  The [[.t]] in [[Int.t]] is conventional: when a "
                             ,
                       ";  module exports one, primary abstract type—like an "
                             ,
                         ";  array, a list, or a hash table, for example—the "
                             ,
                         ";  abstract type component is conventionally called  "
                             ,
                        ";  [[t]]. For example, we have [[Int.t]], the type of "
                             ,
                           ";  integers; [[IntArray.t]], the type of arrays of "
                             ,
                             ";  integers; [[IntList.t]], the type of lists of "
                             ,
                     ";  integers; and so on. This convention is borrowed from "
                             ,
                             ";  \\modula3 [cite nelson:systems-modula,        "
                             ,
                            ";  horning:useful-interfaces, hanson:interfaces]. "
                             ,
                              ";                                               "
                             ,
                       ";  The [[.t]] convention is useful, but you might like "
                             ,
                       ";  to continue to use primitive types defined in other "
                             ,
                       ";  chapters, including [[int]], [[bool]], [[sym]], and "
                             ,
                            ";  [[unit]]. In \\mcl, these types are defined as "
                             ,
                              ";  abbreviations:                               "
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             , "(type int  Int.t)"
                             , "(type bool Bool.t)"
                             , "(type unit Unit.t)"
                             , "(type sym  Sym.t)"
                             ,
                              ";  Module types                                 "
                             ,
                              ";                                               "
                             ,
                          ";  When we build a system, whatever we need to know "
                             ,
                      ";  about any module should be written in its interface. "
                             ,
                        ";  And when the interface exports an abstract type t, "
                             ,
                    ";  we don't know—and don't need to know—how values of "
                             ,
                      ";  type t are represented. All we know are t's name and "
                             ,
                  ";  its kind. [In~\\mcl, unlike \\tuscheme\\ or \\uml, every "
                             ,
                         ";  type has kind~\\ktype. Because the type system is "
                             ,
                       ";  already complicated enough.] What we really know is "
                             ,
                     ";  what operations take values of type t as arguments or "
                             ,
                              ";  return them as results. To think about such  "
                             ,
                              ";  operations, we should use the classification "
                             ,
                             ";  described on \\cpageref                       "
                             ,
                              ";  scheme.constructor-observer-mutator:         "
                             ,
                              ";                                               "
                             ,
                             ";   \\tightlist*                                 "
                             ,
                        ";    • A creator or producer creates a new value of "
                             ,
                         ";   type t. A creator doesn't need an existing value "
                             ,
                              ";   of type t; a producer does.                 "
                             ,
                           ";    • An observer provides information about an "
                             ,
                              ";   argument of type t.                         "
                             ,
                       ";    • A mutator has a side effect on an argument of "
                             ,
                              ";   type t.                                     "
                             ,
                              ";                                               "
                             ,
                     ";  Here, as a first example, is the interface to \\mcl's "
                             ,
                           ";  primitive array abstraction. The abstraction is "
                             ,
                       ";  mutable, and it therefore has a mutator. And it has "
                             ,
                              ";  no producers:[*]                             "
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             , "(module-type ARRAY"
                             , " (exports [abstype t]    ;; an array"
                             ,
                          "          [abstype elem] ;; one element of the array"
                             ,
                         "          [new    : (int elem -> t)]        ; creator"
                             ,
                         "          [empty  : (         -> t)]        ; creator"
                             ,
                        "          [size   : (t -> int)]             ; observer"
                             ,
                        "          [at     : (t int -> elem)]        ; observer"
                             ,
                         "          [at-put : (t int elem -> unit)])) ; mutator"
                             ,
                            ";  This code defines module type [[ARRAY]], which "
                             ,
                       ";  exports two types and five operations. We can think "
                             ,
                              ";  of this module type as a promise, which any  "
                             ,
                       ";  implementation must redeem. The [[ARRAY]] interface "
                             ,
                           ";  promises that an implementation will define the "
                             ,
                              ";  following:                                   "
                             ,
                              ";                                               "
                             ,
                             ";   \\tightlist                                  "
                             ,
                        ";    • A type [[t]], which is the type of the array "
                             ,
                      ";    • A type [[elem]], which is the type of an array "
                             ,
                              ";   element                                     "
                             ,
                    ";    • A function [[new]], which creates a new array of "
                             ,
                              ";   a given size, filled with a given element   "
                             ,
                    ";    • A function [[empty]], which creates a new, empty "
                             ,
                              ";   array, not needing an element               "
                             ,
                   ";    • A function [[size]], which says how many elements "
                             ,
                              ";   are in an array                             "
                             ,
                   ";    • Functions [[at]] and [[at-put]], which look up or "
                             ,
                              ";   update an individual element                "
                             ,
                              ";                                               "
                             , ""
                             ,
                    ";  In \\mcl, the type of a generic module is written like "
                             ,
                        ";  a function type, except that each formal parameter "
                             ,
                      ";  gets a name (so that later parameters and the result "
                             ,
                             ";  type may refer to it), and the parameters are "
                             ,
                     ";  separated from the result type by a ``module arrow'', "
                             ,
                  ";  written [[–m->]]. Here, for example, is the type of \\ "
                             ,
                              ";  mcl's predefined, generic [[Array]] module:  "
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             , "(module-type GENERIC-ARRAY"
                             , " ([Elem : (exports [abstype t])] --m->"
                             , "     (exports [abstype t]        ;; an array"
                             ,
                  "              [type elem Elem.t] ;; one element of the array"
                             ,
                    "              [new    : (int elem -> t)]         ; creator"
                             ,
                    "              [empty  : (         -> t)]         ; creator"
                             ,
                   "              [size   : (t -> int)]              ; observer"
                             ,
                   "              [at     : (t int -> elem)]         ; observer"
                             ,
                    "              [at-put : (t int elem -> unit)]))) ; mutator"
                             ,
                      ";  Instantiation of a generic module is very similar to "
                             ,
                         ";  the instantiation of a polymorphic value in Typed "
                             ,
                       ";  uScheme, but to remind ourselves of the distinction "
                             ,
                       ";  between a generic module in \\mcl and a polymorphic "
                             ,
                              ";  value in Typed uScheme, we write a generic   "
                             ,
                             ";  instantiation using keyword [[@m]]. Here, for "
                             ,
                       ";  example, is the definition of the predefined module "
                             ,
                              ";  [[IntArray]]:                                "
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             , "(module IntArray (@m Array Int))"
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                              ";   + <  =       negated                        "
                             ,
                              ";   - >  !=                                     "
                             ,
                              ";   * <= print                                  "
                             ,
                              ";   / >= println                                "
                             ,
                              ";                                               "
                             ,
                    ";  Names that are overloaded in \\mcl's initial basis [*] "
                             ,
                              ";  [*]                                          "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                     ";  In \\mcl, you overload a name by putting a function's "
                             ,
                     ";  qualified name in an [[overload]] definition. \\mcl's "
                             ,
                      ";  initial basis overloads arithmetic, comparisons, and "
                             ,
                             ";  printing (\\crefmcl.table.overloaded):        "
                             ,
           ";  <predefined Molecule types, functions, and modules ((elided))>= "
                             ,
                             ";  More programming examples, possibly to become "
                             ,
                              ";  exercises                                    "
                             ,
                              ";                                               "
                             ,
                              ";  Bit sets                                     "
                             ,
                              ";                                               "
                             ,
                        ";  (val newline (Char new: 10)) (val left-round (Char "
                             ,
                     ";  new: 40)) (val space (Char new: 32)) (val right-round "
                             ,
                       ";  (Char new: 41)) (val semicolon (Char new: 59)) (val "
                             ,
                         ";  left-curly (Char new: 123)) (val quote (Char new: "
                             ,
                              ";  39)) (val right-curly (Char new: 125)) (val  "
                             ,
                       ";  left-square (Char new: 91)) (val right-square (Char "
                             ,
                              ";  new: 93))                                    "
                             ,
                              ";                                               "
                             ,
                              ";  <definition of module [[Char]]>=             "
                             , "(module [Char : (exports [abstype t]"
                             , "                         [new : (int -> t)]"
                             , "                         [left-curly : t]"
                             , "                         [right-curly : t]"
                             , "                         [left-round : t]"
                             , "                         [right-round : t]"
                             , "                         [left-square : t]"
                             , "                         [right-square : t]"
                             , "                         [newline : t]"
                             , "                         [space : t]"
                             , "                         [semicolon : t]"
                             , "                         [quote : t]"
                             , "                         [=  : (t t -> bool)]"
                             , "                         [!= : (t t -> bool)]"
                             , "                         [print : (t -> unit)]"
                             ,
                            "                         [println : (t -> unit)])]"
                             , ""
                             , "  (type t int)"
                             , "  (define int new ([n : int]) n)"
                             ,
                          ";    As an example of representation hiding, module "
                             ,
                    ";    [[Char]] is sealed with a signature that declares \\ "
                             ,
                    ";    monobox[abstype t]. Inside [[Char]], type [[Char.t]] "
                             ,
                     ";    is defined as type [[int]], and the values exported "
                             ,
                            ";    from module [[Char]] are just integers:      "
                             ,
                         ";    <definitions of values exported from [[Char]]>= "
                             , "  (val newline 10)   "
                             , "  (val space   32)   "
                             , "  (val semicolon    59)   "
                             , "  (val quote        39)   "
                             , "  (val left-round    40)"
                             , "  (val right-round   41)"
                             , "  (val left-curly   123)"
                             , "  (val right-curly  125)"
                             , "  (val left-square   91)"
                             , "  (val right-square  93)"
                             , "                          "
                             , "  (val = Int.=)"
                             , "  (val != Int.!=)"
                             , "                          "
                             , "  (val print Int.printu)"
                             ,
                   "  (define unit println ([c : t]) (print c) (print newline))"
                             , ")   "
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             , "(overload Int.+ Int.-  Int.* Int./ Int.negated"
                             ,
                              "          Int.= Int.!= Int.< Int.> Int.<= Int.>="
                             , "          Int.print Int.println)"
                             ,
                             "(overload Bool.= Bool.!= Bool.print Bool.println)"
                             ,
                              "(overload Sym.=  Sym.!=  Sym.print  Sym.println)"
                             ,
                             "(overload Char.= Char.!= Char.print Char.println)"
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                             ";  <\\mcl's predefined module types>=            "
                             , "(module-type INT"
                             ,
                 "  (exports [abstype t]                 [<  : (t t -> Bool.t)]"
                             ,
                 "           [+ : (t t -> t)]            [<= : (t t -> Bool.t)]"
                             ,
                 "           [- : (t t -> t)]            [>  : (t t -> Bool.t)]"
                             ,
                 "           [* : (t t -> t)]            [>= : (t t -> Bool.t)]"
                             ,
                 "           [/ : (t t -> t)]            [=  : (t t -> Bool.t)]"
                             ,
                 "           [negated : (t -> t)]        [!= : (t t -> Bool.t)]"
                             , "           [print   : (t -> Unit.t)]"
                             , "           [println : (t -> Unit.t)]))"
                             ,
                              ";  Predefined modules and module types          "
                             ,
                              ";                                               "
                             ,
                              ";  Unused predefined module types               "
                             ,
                              ";                                               "
                             ,
                    ";  In addition to the [[ARRAY]] module type defined in \\ "
                             ,
                             ";  chunkrefmcl.chunk.ARRAY, \\mcl defines        "
                             ,
                              ";                                               "
                             ,
                             ";  <\\mcl's predefined module types>=            "
                             , "(module-type PRINTS"
                             , "   (exports [abstype t]"
                             , "            [print : (t -> unit)]"
                             , "            [println : (t -> unit)]))"
                             ,
                             ";  <\\mcl's predefined module types>=            "
                             , "(module-type BOOL"
                             , "   (exports [abstype t]"
                             , "            [#f : t]"
                             , "            [#t : t]))"
                             ,
                   " ;;;; omitted: and, or, not, similar?, copy, print, println"
                             ,
                             ";  <\\mcl's predefined module types>=            "
                             , "(module-type SYM"
                             , "   (exports [abstype t]"
                             , "            [=  : (t t -> Bool.t)]"
                             , "            [!= : (t t -> Bool.t)]))"
                             ,
                           " ;;;; omitted: hash, similar?, copy, print, println"
                             ,
                             ";  <\\mcl's predefined module types>=            "
                             , "(module-type ORDER"
                             , "  (exports [abstype t]"
                             , "           [LESS : t]"
                             , "           [EQUAL : t]"
                             , "           [GREATER : t]))"
                             , ""
                             , "(module [Order : ORDER]"
                             , "  (data t"
                             , "    [LESS : t]"
                             , "    [EQUAL : t]"
                             , "    [GREATER : t]))"
                             , ""
                             , "(module-type RELATIONS"
                             , "  (exports [abstype t]"
                             , "           [<  : (t t -> Bool.t)]"
                             , "           [<= : (t t -> Bool.t)]"
                             , "           [>  : (t t -> Bool.t)]"
                             , "           [>= : (t t -> Bool.t)]"
                             , "           [=  : (t t -> Bool.t)]"
                             , "           [!= : (t t -> Bool.t)]))"
                             , ""
                             ,
                       "(generic-module [Relations : ([M : (exports [abstype t]"
                             ,
    "                                            [compare : (t t -> Order.t)])]"
                             ,
                         "                               --m-> (allof RELATIONS"
                             ,
         "                                            (exports [type t M.t])))]"
                             , "  (type t M.t)"
                             , "  (define bool < ([x : t] [y : t])"
                             , "     (case (M.compare x y)"
                             , "        [Order.LESS #t]"
                             , "        [_    #f]))"
                             , "  (define bool > ([x : t] [y : t])"
                             , "     (case (M.compare y x)"
                             , "        [Order.LESS #t]"
                             , "        [_    #f]))"
                             , "  (define bool <= ([x : t] [y : t])"
                             , "     (case (M.compare x y)"
                             , "        [Order.GREATER #f]"
                             , "        [_       #t]))"
                             , "  (define bool >= ([x : t] [y : t])"
                             , "     (case (M.compare y x)"
                             , "        [Order.GREATER #f]"
                             , "        [_       #t]))"
                             , "  (define bool = ([x : t] [y : t])"
                             , "     (case (M.compare x y)"
                             , "        [Order.EQUAL #t]"
                             , "        [_     #f]))"
                             , "  (define bool != ([x : t] [y : t])"
                             , "     (case (M.compare x y)"
                             , "        [Order.EQUAL #f]"
                             , "        [_     #t])))"
                             , ""
                             ,
                              ";  Resizeable arrays                            "
                             ,
                              ";                                               "
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             ,
                             ";  Program design with abstract data types:\\    "
                             ,
                        ";  breakAbstractions, representations, and invariants "
                             ,
                              ";                                               "
                             ,
                             ";  [*] >p\\bothwidth                             "
                             ,
                              ";                                               "
                             ,
                     ";  The role of an abstract data type varies depending on "
                             ,
                     ";  what code is using it. Inside the module that defines "
                             ,
                     ";  the type, in its implementation, the abstract type is "
                             ,
                      ";  treated as a representation. Outside the module that "
                             ,
                       ";  defines the type, in client code, the abstract type "
                             ,
                              ";  is treated as an abstraction. Of the two,    "
                             ,
                       ";  representations are easier to understand—from the "
                             ,
                              ";  moment we learn to program, we work with     "
                             ,
                             ";  representations. Examples include records and "
                             ,
                              ";  structs, pointers, S-expressions, arrays,    "
                             ,
                              ";  constructed data, and so on.                 "
                             ,
                              ";                                               "
                             ,
                             ";  \\stdbreak Abstractions are less concrete.    "
                             ,
                          ";  An abstraction is what a thing stands for in the "
                             ,
                     ";  world of ideas, not the world of code. An abstraction "
                             ,
                           ";  might come from math, like a set, a graph, or a "
                             ,
                        ";  complex number. Or it might come from a particular "
                             ,
                              ";  domain, like a dictionary, a probability     "
                             ,
                              ";  distribution, or an open file handle.        "
                             ,
                              ";                                               "
                             ,
                       ";  \\stdbreak The role of an abstraction is to express "
                             ,
                            ";  the promises that an interface makes to client "
                             ,
                            ";  code—to say what the exported operations do. "
                             ,
                        ";  For example, an operation in one module might take "
                             ,
                     ";  the union of two sets; an operation in another module "
                             ,
                          ";  might write a string to a file. A person writing "
                             ,
                       ";  client code can do their job without having to know "
                             ,
                         ";  what's happening behind the abstraction barriers. "
                             ,
                              ";                                               "
                             ,
                    ";  \\stdbreak The role of a representation is to keep the "
                             ,
                    ";  promises—or rather, to enable a programmer to do so. "
                             ,
                     ";  \\stdbreak Another way to think about abstraction and "
                             ,
                        ";  representation is that if we know the abstraction, "
                             ,
                      ";  we know what an operation does, \\stdbreak but if we "
                             ,
                       ";  don't know the representation, we're shielded from  "
                             ,
                      ";  how. \\stdbreak When representations are hidden, our "
                             ,
                         ";  client code doesn't have to know that to take the "
                             ,
                        ";  union of two sets, we must merge two binary search "
                             ,
                       ";  trees, or to write a string to a file, we must copy "
                             ,
                              ";  bytes into a buffer.                         "
                             ,
                              ";                                               "
                             ,
                        ";  \\stdbreak Abstraction meets representation in the "
                             ,
                             ";  implementation of a module. To illuminate the "
                             ,
                           ";  relationship between abstraction and \\stdbreak "
                             ,
                   ";  representation—and thereby to clarify our obligations "
                             ,
                              ";  as implementors, we have two tools: the      "
                             ,
                     ";  representation invariant and the abstraction function "
                             ,
                              ";  .                                            "
                             ,
                              ";                                               "
                             ,
                            ";    • A representation invariant tells us what "
                             ,
                         ";   representations are meaningful: a representation "
                             ,
                              ";   stands for an abstraction only if the       "
                             ,
                       ";   representation satisfies the invariant. \\stdbreak "
                             ,
                              ";   An invariant can be a property as simple as "
                             ,
                            ";   ``keys in the left subtree are smaller'' or a "
                             ,
                              ";   property so complicated as to demand to be  "
                             ,
                           ";   written mathematically. \\stdbreak Interesting "
                             ,
                              ";   data structures often satisfy multiple      "
                             ,
                         ";   representation invariants. These may be referred "
                             ,
                              ";   to individually, and they may also be       "
                             ,
                              ";   collectively called ``the invariant.''      "
                             ,
                              ";                                               "
                             ,
                         ";   \\stdbreak For example, the order invariant in a "
                             ,
                              ";   binary search tree guarantees that a search "
                             ,
                        ";   function will find an object, if present, without "
                             ,
                             ";   having to look at every node of the tree. \\ "
                             ,
                          ";   stdbreak A serious, sophisticated binary search "
                             ,
                            ";   tree also has a balance invariant. \\stdbreak "
                             ,
                              ";   There are many different forms of balance   "
                             ,
                            ";   invariant, but they all guarantee that search "
                             ,
                              ";   takes a number of steps that is at most     "
                             ,
                          ";   logarithmic in the number of nodes in the tree. "
                             ,
                              ";                                               "
                             ,
                             ";   \\stdbreak                                   "
                             ,
                   ";    • An abstraction function tells us how a meaningful "
                             ,
                        ";   representation relates to the abstraction used in "
                             ,
                         ";   the specification of the interface. An effective "
                             ,
                          ";   abstraction function maps the representation to "
                             ,
                        ";   an abstraction that is (mathematically) as simple "
                             ,
                              ";   as possible. The abstraction function for a "
                             ,
                          ";   binary search tree, for example, usually maps a "
                             ,
                            ";   tree structure to a simple set or finite map. "
                             ,
                              ";                                               "
                             ,
                              ";   As an example, suppose I represent a set of "
                             ,
                          ";   values as a binary search tree, which is either "
                             ,
                        ";   [[Empty]] or is \\monobox(Node l v r), where v is "
                             ,
                        ";   a value and l and r are binary search trees. Then "
                             ,
                       ";   I can specify the abstraction function \\absfun in "
                             ,
                       ";   just a couple of lines: {align*} \\absfun\\monobox "
                             ,
                              ";   ([[Empty]]) --- = { }                       "
                             ,
                    ";   \\absfun\\monobox(Node l v r) --- = \\absfun(l) \\cup "
                             ,
                            ";   \\absfun(r) \\cup{v} {align*}                 "
                             ,
                              ";                                               "
                             ,
                       ";  Example abstractions, with possible representations "
                             ,
                              ";                                               "
                             ,
                          ";  To develop our understanding of abstractions and "
                             ,
                           ";  representations, let's see some examples: sets, "
                             ,
                       ";  dictionaries, priority queues, and complex numbers. "
                             ,
                        ";  For each abstraction, I sketch operations, suggest "
                             ,
                      ";  possible representations, and present the invariants "
                             ,
                        ";  of each representation. I also say something about "
                             ,
                              ";  abstraction functions and a bit about which  "
                             ,
                              ";  representations are good for what.           "
                             ,
                              ";                                               "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                              ";   Abstraction                  Operations     "
                             ,
                         ";                                At least [[empty]]/ "
                             ,
                        ";                                [[new]], [[insert]], "
                             ,
                              ";                                [[delete]],    "
                             ,
                              ";   Set                          [[member?]];   "
                             ,
                              ";                                possibly also  "
                             ,
                              ";                                [[empty?]],    "
                             ,
                        ";                                [[size]], [[union]], "
                             ,
                         ";                                [[inter]], [[diff]] "
                             ,
                             ";   [\\heavyrulewidth]            Invariant      "
                             ,
                              ";   Representation                              "
                             ,
                              ";   Array                        No element is  "
                             ,
                              ";                                repeated.      "
                             ,
                              ";   List                         No element is  "
                             ,
                              ";                                repeated.      "
                             ,
                              ";                                No element is  "
                             ,
                          ";   Sorted list                  repeated; elements "
                             ,
                              ";                                are sorted.    "
                             ,
                              ";                                No element is  "
                             ,
                           ";                                repeated; smaller "
                             ,
                        ";                                elements are in left "
                             ,
                            ";   Binary search tree           subtrees; larger "
                             ,
                             ";                                elements are in "
                             ,
                             ";                                right subtrees; "
                             ,
                        ";                                perhaps some sort of "
                             ,
                          ";                                balance invariant. "
                             ,
                             ";   [\\heavyrulewidth]                           "
                             ,
                              ";   Abstraction functions                       "
                             ,
                             ";   \\absfunpar The abstraction                  "
                             ,
                              ";   function combines all                       "
                             ,
                              ";   elements of the                             "
                             ,
                              ";   representation. Algebraic                   "
                             ,
                              ";   laws for a binary search                    "
                             ,
                              ";   tree are shown above; for a                 "
                             ,
                              ";   list, the laws of the                       "
                             ,
                             ";   abstraction function are \\                  "
                             ,
                             ";   absfun(\\monobox[['()]]) = {                 "
                             ,
                            ";   } and \\absfun\\monobox(cons v                "
                             ,
                          ";   \\vs) = {v}\\cup\\absfun(\\vs).                 "
                             ,
                              ";                                               "
                             ,
                              ";  Possible representations of a set [*]        "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                              ";   Abstraction                  Operations     "
                             ,
                         ";                                At least [[empty]]/ "
                             ,
                        ";                                [[new]], [[insert]]/ "
                             ,
                              ";                                [[bind]],      "
                             ,
                              ";   Dictionary                   [[delete]],    "
                             ,
                        ";                                [[lookup]]/[[find]]; "
                             ,
                              ";                                possibly also  "
                             ,
                              ";                                [[empty?]],    "
                             ,
                        ";                                [[size]], and others "
                             ,
                             ";   [\\heavyrulewidth]            Invariant      "
                             ,
                              ";   Representation                              "
                             ,
                         ";                                Every key is paired "
                             ,
                           ";   Association list             with the value it "
                             ,
                              ";                                maps to.       "
                             ,
                        ";                                Every key-value pair "
                             ,
                              ";                                is stored in a "
                             ,
                         ";                                bucket in an array, "
                             ,
                         ";   \\bigstrut Hash table         the index of which "
                             ,
                        ";                                is a function of the "
                             ,
                        ";                                array's size and the "
                             ,
                           ";                                element's integer "
                             ,
                              ";                                hash.          "
                             ,
                          ";                                Pairs with smaller "
                             ,
                            ";                                keys are in left "
                             ,
                       ";   \\bigstrut Binary search tree subtrees; pairs with "
                             ,
                          ";                                larger keys are in "
                             ,
                             ";                                right subtrees. "
                             ,
                             ";   [\\heavyrulewidth]                           "
                             ,
                              ";   Abstraction functions                       "
                             ,
                             ";   \\absfunpar The easy way to                  "
                             ,
                              ";   specify an abstraction                      "
                             ,
                              ";   function is to treat the                    "
                             ,
                              ";   abstraction as an                           "
                             ,
                              ";   environment, which is to say                "
                             ,
                              ";   a set of key-value pairs,                   "
                             ,
                            ";   and to use the \\envplus      = \\emptyenv    "
                             ,
                             ";   operation defined on \\                      "
                             ,
                              ";   cpagerefscheme.envplus. For                 "
                             ,
                              ";   example, the abstraction                    "
                             ,
                              ";   function for an association                 "
                             ,
                            ";   list is {align*} \\absfun(\\                  "
                             ,
                              ";   monobox'())                                 "
                             ,
                       ";   \\absfun(\\monobox(cons (pair  = \\absfun(\\ps) \\ "
                             ,
                            ";   k v) \\ps))                   envplus{k |->v} "
                             ,
                              ";                                {align*}       "
                             ,
                              ";                                               "
                             ,
                              ";  Possible representations of a dictionary [*] "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                          ";  Our first example abstraction is a set, which is "
                             ,
                        ";  defined by the elements it contains. Some possible "
                             ,
                      ";  representations and their invariants are shown in \\ "
                             ,
                              ";  crefmcl.fig.set.                             "
                             ,
                              ";                                               "
                             ,
                         ";  An abstraction can be explained to client code by "
                             ,
                       ";  specifying the effect of each operation informally, "
                             ,
                              ";  or it can be specified formally by showing   "
                             ,
                              ";  relationships among the operations. If the   "
                             ,
                         ";  abstraction is immutable, these relationships can "
                             ,
                     ";  usually be specified by algebraic laws; here are some "
                             ,
                       ";  that specify relationships among set operations:[*] "
                             ,
                         ";  {laws} \\monolaw(member? v empty)[[#f]] \\monolaw "
                             ,
                       ";  (member? v (insert s v))[[#t]] \\monolaw(member? v' "
                             ,
                       ";  (insert s v)) (member? v' s), where v!=v' \\monolaw "
                             ,
                    ";  [[(empty? empty)]][[#t]] \\monolaw(empty? (insert s v) "
                             ,
                       ";  [[#f]] \\monolaw(delete empty v)[[empty]] \\monolaw "
                             ,
                      ";  (delete (insert s v) v)(delete s v) \\monolaw(delete "
                             ,
                      ";  (insert s v') v) (insert (delete s v) v'), where v!= "
                             ,
                     ";  v' {laws} You can try out algebraic laws for yourself "
                             ,
                             ";  in \\crefpagemcl.ex.alist-type-and-laws.      "
                             ,
                              ";                                               "
                             ,
                      ";  If a set abstraction is mutable, the behavior of its "
                             ,
                         ";  operations can still be specified using algebraic "
                             ,
                     ";  laws, but with a level of indirection: algebraic laws "
                             ,
                         ";  are used to specify an immutable abstraction, and "
                             ,
                              ";  that abstraction is used to specify how each "
                             ,
                        ";  operation may depend on or change the state of the "
                             ,
                       ";  set. The details are beyond the scope of this book. "
                             ,
                              ";                                               "
                             ,
                          ";  Our next example abstraction is a dictionary (\\ "
                             ,
                      ";  crefmcl.fig.dictionary). A dictionary, also called a "
                             ,
                     ";  ``table,'' ``associative array,'' ``environment,'' or "
                             ,
                      ";  ``finite map,'' is defined by a mapping from keys to "
                             ,
                              ";  values.                                      "
                             ,
                              ";                                               "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                              ";   Abstraction                    Operations   "
                             ,
                        ";                                  At least [[empty]] "
                             ,
                              ";                                  /[[new]],    "
                             ,
                              ";                                  [[insert]],  "
                             ,
                           ";                                  [[empty?]], and "
                             ,
                           ";   Priority queue                 [[delete-min]]; "
                             ,
                             ";                                  possibly also "
                             ,
                              ";                                  [[size]],    "
                             ,
                             ";                                  [[find-min]], "
                             ,
                              ";                                  [[merge]]    "
                             ,
                             ";   \\midtoprule Representation     Invariant    "
                             ,
                            ";                                  List is sorted "
                             ,
                         ";                                  with the smallest "
                             ,
                            ";   List                           element at the "
                             ,
                        ";                                  front (inefficient "
                             ,
                            ";                                  unless small). "
                             ,
                        ";                                  Element at index i "
                             ,
                        ";                                  is not larger than "
                             ,
                          ";   \\bigstrut Array                the elements at "
                             ,
                            ";                                  indices 2i and "
                             ,
                             ";                                  2i+1, if any. "
                             ,
                        ";                                  Element at node is "
                             ,
                           ";                                  not larger than "
                             ,
                         ";   \\bigstrut Binary tree          elements at left "
                             ,
                          ";                                  and right child, "
                             ,
                              ";                                  if any.      "
                             ,
                         ";                                  Binary tree, with "
                             ,
                            ";                                  the additional "
                             ,
                            ";                                  invariant that "
                             ,
                       ";   \\bigstrut Leftist heap         every left subtree "
                             ,
                            ";                                  is at least as "
                             ,
                              ";                                  high as the  "
                             ,
                             ";                                  corresponding "
                             ,
                            ";                                  right subtree. "
                             ,
                             ";   [\\heavyrulewidth] Abstraction               "
                             ,
                              ";   functions                                   "
                             ,
                             ";   \\absfunpar Perhaps because                  "
                             ,
                              ";   bags aren't often used in                   "
                             ,
                              ";   mathematical descriptions,                  "
                             ,
                              ";   I'm not aware of widely                     "
                             ,
                              ";   accepted notation for bags and              "
                             ,
                              ";   operations upon them—which                "
                             ,
                              ";   makes it difficult to notate                "
                             ,
                              ";   abstraction functions. But the              "
                             ,
                              ";   functions themselves are                    "
                             ,
                              ";   simple: take all the elements               "
                             ,
                              ";   from the representation, and                "
                             ,
                              ";   toss them into a bag. For an                "
                             ,
                              ";   alternative, more precise                   "
                             ,
                              ";   approach to priority queues,                "
                             ,
                             ";   see \\crefpagemcl.ex.pq-spec.                "
                             ,
                              ";                                               "
                             ,
                          ";  Possible representations of a priority queue [*] "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                      ";  Our next example abstraction is a priority queue (\\ "
                             ,
                      ";  crefmcl.fig.pq).[*] A priority queue is a collection "
                             ,
                        ";  of values—technically a ``bag'' or ``multiset,'' "
                             ,
                     ";  because there may be duplicates—which provides fast "
                             ,
                              ";  access to the smallest value. Again, we have "
                             ,
                     ";  different abstractions and different cost models. For "
                             ,
                      ";  a mutable priority queue, an array is very effective "
                             ,
                       ";  (\\crefmcl.pqueue); for an immutable priority queue "
                             ,
                        ";  with an efficient [[merge]] operation, I recommend "
                             ,
                             ";  the leftist heap (\\crefmcl.leftist).         "
                             ,
                              ";                                               "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                              ";   Abstraction                  Operations     "
                             ,
                         ";                                Constructor, vector "
                             ,
                          ";                                addition, distance "
                             ,
                        ";   2D point                     from origin, scaling "
                             ,
                              ";                                by a number,   "
                             ,
                              ";                                translation,   "
                             ,
                              ";                                rotation, ...  "
                             ,
                             ";   [\\heavyrulewidth]            Invariant      "
                             ,
                              ";   Representation                              "
                             ,
                              ";   Cartesian coordinates (x, y) None           "
                             ,
                        ";   \\bigstrut Polar coordinates  r >=0, possibly -pi "
                             ,
                              ";   (r, theta)                   <=theta< pi    "
                             ,
                       ";   \\bigstrut Quadrant-magnitude |x|>=0, |y|>=0, 0<=Q "
                             ,
                              ";   (Q, |x|, |y|)                < 4            "
                             ,
                             ";   [\\heavyrulewidth]                           "
                             ,
                              ";   Abstraction functions                       "
                             ,
                             ";   \\absfunpar For the Cartesian                "
                             ,
                              ";   representation, the                         "
                             ,
                              ";   abstraction function is the                 "
                             ,
                              ";   identity function. For the                  "
                             ,
                              ";   polar representation, it is                 "
                             ,
                             ";   \\absfun(r,theta) = (r cos                   "
                             ,
                              ";   theta, r sintheta).                         "
                             ,
                              ";                                               "
                             ,
                     ";  Possible representations of a point in two dimensions "
                             ,
                              ";  [*]                                          "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                     ";  Our next example abstraction returns to the beginning "
                             ,
                     ";  of this chapter: it is a two-dimensional point on the "
                             ,
                    ";  plane (\\crefmcl.fig.2dpoint). Such a point is defined "
                             ,
                            ";  by its x and y coordinates. If all you have is "
                             ,
                         ";  integers, Cartesian coordinates are the only game "
                             ,
                  ";  in town—though \\crefpagemcl.ex.mqpoint invites you to "
                             ,
                      ";  play with the a representation that stores a point's "
                             ,
                              ";  quadrant and the magnitudes of the x and y   "
                             ,
                     ";  coordinates. But if you have access to floating-point "
                             ,
                             ";  numbers, and if you plan lots of rotations or "
                             ,
                        ";  magnitude tests, polar coordinates could be a good "
                             ,
                              ";  choice.                                      "
                             ,
                              ";                                               "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                              ";   Abstraction          Operations             "
                             ,
                          ";   Complex number       Constructor, [[+]], [[-]], "
                             ,
                           ";                        [[*]], [[/]], [[negated]] "
                             ,
                             ";   [\\heavyrulewidth]    Invariant              "
                             ,
                              ";   Representation                              "
                             ,
                              ";   Cartesian            None                   "
                             ,
                              ";   coordinates (x, y)                          "
                             ,
                       ";   \\bigstrut Polar      r >=0, possibly -pi<=theta<  "
                             ,
                              ";   coordinates (r,      pi                     "
                             ,
                              ";   theta)                                      "
                             ,
                              ";                                               "
                             ,
                          ";  Possible representations of a complex number [*] "
                             ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                             ,
                              ";                                               "
                             ,
                     ";  Our final example abstraction is a complex number (\\ "
                             ,
                     ";  crefmcl.fig.complex). Such a number is defined by its "
                             ,
                          ";  real and imaginary parts. The set of all complex "
                             ,
                              ";  numbers is isomorphic to the set of all      "
                             ,
                       ";  two-dimensional points, but two complex numbers can "
                             ,
                        ";  meaningfully be multiplied to form a third complex "
                             ,
                      ";  number, which is not true of two-dimensional points. "
                             ,
                              ";                                               "
                             ,
                             ";  The examples above illustrate an idea that is "
                             ,
                              ";  indispensable when building large systems:   "
                             ,
                              ";  distinguish abstraction from implementation. "
                             ,
                              ";                                               "
                             ,
                              ";  Mutable and immutable abstractions           "
                             ,
                              ";                                               "
                             ,
                        ";  If an abstraction has a state that can change over "
                             ,
                            ";  time, it's mutable. Otherwise, it's immutable. "
                             ,
                         ";  A mutable abstraction almost always has a mutable "
                             ,
                            ";  representation. [In~exceptional circumstances, "
                             ,
                              ";  a~mutable abstraction may have an immutable  "
                             ,
                       ";  representation that refers to mutable state located "
                             ,
                       ";  elsewhere.] An immutable abstraction usually has an "
                             ,
                       ";  immutable representation, but it can have a mutable "
                             ,
                   ";  representation—a classic example is an immutable data "
                             ,
                             ";  structure with a mutable cache, as in \\      "
                             ,
                             ";  crefsmall.ex.method-cache on \\               "
                             ,
                              ";  pageofchapsmall.ex.method-cache.             "
                             ,
                              ";                                               "
                             ,
                           ";  Mutability isn't arbitrary; for example, atomic "
                             ,
                      ";  values—integers, Booleans, characters, enumeration "
                             ,
                       ";  literals, and so on—are expected to be immutable. "
                             ,
                            ";  After all, what could it mean to ``mutate 3''? "
                             ,
                         ";  When a programmer wants to use atomic values with "
                             ,
                        ";  mutable state, he or she puts the immutable atomic "
                             ,
                              ";  value inside some sort of mutable container: "
                             ,
                     ";  a variable, a mutable reference cell, or a field of a "
                             ,
                        ";  mutable record. By contrast, aggregate values like "
                             ,
                           ";  strings, arrays, and records, which store other "
                             ,
                   ";  values inside, are often mutable—though in functional "
                             ,
                      ";  languages, it's more typical for strings and records "
                             ,
                            ";  to be immutable, and to offer both mutable and "
                             ,
                              ";  immutable arrays.                            "
                             ,
                              ";                                               "
                             ,
                           ";  As a designer, you won't always know whether an "
                             ,
                        ";  abstraction should be mutable or immutable. It can "
                             ,
                      ";  help to focus on individual operations. Does a given "
                             ,
                      ";  operation work better as a producer (immutable) or a "
                             ,
                           ";  mutator (mutable)? How does the decision affect "
                             ,
                       ";  costs? Operating on an immutable representation may "
                             ,
                              ";  require allocation or copying that a mutable "
                             ,
                       ";  representation would make unnecessary. For example, "
                             ,
                         ";  to change one element of a mutable array, we just "
                             ,
                       ";  change the element. But to change one element of an "
                             ,
                            ";  immutable array, we create an entire new array "
                             ,
                           ";  differing only in that one element, leaving the "
                             ,
                       ";  original unchanged. The first cost is constant; the "
                             ,
                              ";  second is linear in the size of the array.   "
                             ,
                              ";                                               "
                             ,
                      ";  If immutability is so expensive, why use it? Because "
                             ,
                        ";  it's simpler. Immutable abstractions are easier to "
                             ,
                        ";  specify, easier to understand, easier to test, and "
                             ,
                       ";  easier to share. When using immutable abstractions, "
                             ,
                      ";  you never have to reason about a sequence of changes "
                             ,
                   ";  or other events—the same function applied to the same "
                             ,
                       ";  value always returns the same result. Operations on "
                             ,
                       ";  immutable abstractions are independent of the order "
                             ,
                      ";  of evaluation. And when an abstraction is immutable, "
                             ,
                         ";  you don't need a protocol to decide how it can be "
                             ,
                    ";  shared and who has permission to mutate it—everybody "
                             ,
                     ";  shares it, and nobody mutates it. Judge for yourself; "
                             ,
                        ";  compare your experience programming with immutable "
                             ,
                              ";  abstractions in micro-Scheme and ML to your  "
                             ,
                       ";  experience programming with mutable abstractions in "
                             ,
                            ";  C, \\mcl, and uSmalltalk (\\crefsmall.chap).   "
                             ,
                              ";                                               "
                             ,
                      ";  Sometimes the question ``mutable or immutable?'' has "
                             ,
                       ";  this answer: ``both.'' For example, if I'm using an "
                             ,
                        ";  association list to represent an environment in an "
                             ,
                       ";  interpreter, I want an immutable [[alist]]—that's "
                             ,
                              ";  going to make it easy to implement [[let]]   "
                             ,
                             ";  expressions and closures. But if I'm using an "
                             ,
                      ";  association list to implement a sparse array, I want "
                             ,
                          ";  a mutable [[alist]]—that's going to reduce the "
                             ,
                     ";  allocation cost of an update from linear to constant. "
                             ,
                      ";  When possible, design mutable abstractions in tandem "
                             ,
                      ";  with immutable ones. That way you'll always have the "
                             ,
                              ";  one you want when you want it.               "
                             ,
                              ";                                               "
                             ,
                      ";  If you struggle to remember the primary consequences "
                             ,
                    ";  of mutability in abstractions—immutable abstractions "
                             ,
                     ";  are simpler, but they may require more allocation and "
                             ,
                       ";  copying—it may help to think about implementation "
                             ,
                       ";  costs. Atomic values that fit in machine registers, "
                             ,
                      ";  like Booleans and small integers, should probably be "
                             ,
                       ";  immutable, since they don't have to be allocated on "
                             ,
                       ";  the heap, and copying one is no more expensive than "
                             ,
                     ";  computing one. Large values that are allocated on the "
                             ,
                              ";  heap, however, might better default to       "
                             ,
                         ";  mutable—particularly if you want programmers to "
                             ,
                      ";  understand the cost of copying, or if you don't have "
                             ,
                         ";  a fancy allocator. And if you do want to allocate "
                             ,
                         ";  immutable values on the heap, you had better make "
                             ,
                              ";  allocation and copying really fast, like the "
                             ,
                           ";  allocator and copying collector described in \\ "
                             ,
                             ";  crefgc.chap. Mature languages that use mostly "
                             ,
                      ";  immutable data—like Haskell, \\ocaml, and Standard "
                             ,
                 ";  ML—are known for fast allocation. [\\haskell\\ programs "
                             ,
                        ";  actually use a ton of mutable representations, but "
                             ,
                       ";  they are almost all ``thunks.'' The~mutability of a "
                             ,
                       ";  thunk is part of \\haskell's operational semantics, "
                             ,
                       ";  but it is not visible to the programmer: a~thunk is "
                             ,
                              ";  an immutable abstraction with a mutable      "
                             ,
                              ";  representation.]                             "
                             ,
                              ";                                               "
                             ,
                         ";  Abstraction plus cost model equals data structure "
                             ,
                              ";                                               "
                             ,
                     ";  Why should we consider multiple representations, both "
                             ,
                         ";  mutable and immutable, for a typical abstraction? "
                             ,
                       ";  In part, because different representations may have "
                             ,
                           ";  different cost models. A cost model exposes the "
                             ,
                          ";  performance tradeoffs made in an implementation: "
                             ,
                      ";  which operations (or combinations of operations) are "
                             ,
                     ";  fast and which are slow. As a designer, you're likely "
                             ,
                          ";  to choose a representation based not only on the "
                             ,
                       ";  abstraction you're trying to implement, but also on "
                             ,
                         ";  the cost model you're looking for. To do this job "
                             ,
                        ";  well requires an understanding of data structures. "
                             ,
                        ";  For example, here are some cost considerations for "
                             ,
                              ";  sets:                                        "
                             ,
                              ";                                               "
                             ,
                    ";    • If a set is small, say a dozen elements or less, "
                             ,
                         ";   and if a mutable set is OK, an array uses memory "
                             ,
                              ";   very efficiently.                           "
                             ,
                        ";    • For a small, immutable set, lists are cheap. "
                             ,
                      ";    • If each set is represented as a list, a simple "
                             ,
                        ";   implementation of [[union]] takes quadratic time. "
                             ,
                         ";   But if each set is represented as a sorted list, "
                             ,
                         ";   set union can be implemented in linear time. The "
                             ,
                         ";   expected costs of [[insert]] and [[member?]] can "
                             ,
                              ";   also drop.                                  "
                             ,
                     ";    • If a set is mutable, and if only a few elements "
                             ,
                        ";   are accessed frequently, a move-to-front list can "
                             ,
                           ";   provide cheap access. A move-to-front list has "
                             ,
                        ";   the same invariant as a regular list, but it also "
                             ,
                         ";   records history: every time an element is looked "
                             ,
                          ";   up or inserted, it is moved to the front of the "
                             ,
                              ";   list. To enable an element to be moved in   "
                             ,
                              ";   constant time, a mutable list is needed.    "
                             ,
                          ";    • For a larger set, a binary search tree can "
                             ,
                              ";   provide an efficient implementation of      "
                             ,
                              ";   [[member?]], provided the tree is somewhat  "
                             ,
                         ";   balanced. One good invariant is that the longest "
                             ,
                        ";   path from the root to a leaf is at most twice the "
                             ,
                           ";   length of the shortest path from the root to a "
                             ,
                        ";   leaf; one tree that satisfies this invariant is a "
                             ,
                        ";   red-black tree. Another, more stringent invariant "
                             ,
                        ";   is that left and right subtree of any node differ "
                             ,
                            ";   in height by at most 1; a tree that satisfies "
                             ,
                              ";   this invariant is an AVL tree.              "
                             ,
                     ";    • A hash table typically requires 20% more memory "
                             ,
                          ";   than a simple list or a binary search tree, but "
                             ,
                           ";   provided the abstraction is mutable, it offers "
                             ,
                              ";   constant-time lookup and insertion.         "
                             ,
                              ";                                               "
                             ,
                       ";  If we know more about the elements of a set, we can "
                             ,
                       ";  consider additional representations, such as a trie "
                             ,
                              ";  or a Patricia tree.                          "
                             ,
                              ";                                               "
                             ,
                      ";  Quite often an abstraction is useful only if certain "
                             ,
                      ";  selected operations have low cost—constant time or "
                             ,
                        ";  logarithmic time, for example. As an example where "
                             ,
                      ";  different cost models come into play, here are three "
                             ,
                         ";  use cases for a common abstraction: the bag. Each "
                             ,
                              ";  use case determines a different cost model.  "
                             ,
                              ";                                               "
                             ,
                    ";    • In my car there is a memory card that contains a "
                             ,
                            ";   bag of all the gas stations in North America. "
                             ,
                        ";   When fuel runs low, the car offers to guide me to "
                             ,
                          ";   the gas station nearest to my current location. "
                             ,
                          ";   Because the computer in my car is not powerful, "
                             ,
                          ";   the bag of gas stations had better come with an "
                             ,
                            ";   efficient ``find nearest to GPS coordinates'' "
                             ,
                             ";   operation—logarithmic in the number of gas "
                             ,
                         ";   stations. One effective implementation is called "
                             ,
                             ";   a 2D-tree (\\crefpageadta.2dtrees of the     "
                             ,
                              ";   Supplement).                                "
                             ,
                              ";                                               "
                             ,
                          ";    • The files I use all the time are stored on "
                             ,
                          ";   solid-state drives, but for images and video, I "
                             ,
                        ";   still use spinning hard drives—my study at home "
                             ,
                           ";   has over 20 terabytes of storage. When data is "
                             ,
                           ";   written to a spinning hard drive, my operating "
                             ,
                        ";   system maintains a bag of pending write requests. "
                             ,
                             ";   To avoid having to wait for the disk to spin "
                             ,
                         ";   around, it needs to issue those requests in just "
                             ,
                        ";   the right order. An effective implementation of a "
                             ,
                           ";   bag that does this is called an I/O scheduler. "
                             ,
                              ";                                               "
                             ,
                             ";    • When I run a discrete-event simulation, "
                             ,
                          ";   it creates events in some order that is hard to "
                             ,
                            ";   predict, and it puts those events into a bag. "
                             ,
                           ";   When events come out of the bag, however, they "
                             ,
                             ";   must come in a particular order: the soonest "
                             ,
                            ";   scheduled event must come first. An effective "
                             ,
                        ";   implementation of a bag that finds the next event "
                             ,
                      ";   quickly—again in logarithmic time—is a priority "
                             ,
                             ";   queue (\\crefpagemcl.pqueue below).          "
                             ,
                              ";                                               "
                             ,
                              ";  Tricks of interface design                   "
                             ,
                              ";                                               "
                             ,
                          ";  [*] The design of an abstraction begins with its "
                             ,
                       ";  interface. Designing interfaces well is an art, but "
                             ,
                      ";  we can develop our art by applying some intellectual "
                             ,
                              ";  tools.                                       "
                             ,
                              ";                                               "
                             ,
                   ";    • Description. Effective design begins with an idea "
                             ,
                          ";   what abstraction is being designed. To describe "
                             ,
                          ";   that idea, you can often use other abstractions "
                             ,
                           ";   that you already know: sequence, product, sum, "
                             ,
                        ";   set, function, finite map, grocery bag, graph, or "
                             ,
                              ";   tree. And the operations defined on these   "
                             ,
                              ";   existing abstractions help you describe the "
                             ,
                           ";   operations you define on your own abstraction. "
                             ,
                              ";                                               "
                             ,
                           ";    • Mutability. As discussed above, immutable "
                             ,
                        ";   abstractions are simpler to specify and test, but "
                             ,
                              ";   mutable abstractions may have a better cost "
                             ,
                           ";   model. If you are designing a new abstraction, "
                             ,
                        ";   start with an immutable version; design a mutable "
                             ,
                              ";   version only if your cost model demands it. "
                             ,
                              ";                                               "
                             ,
                       ";    • Operations and cost model. Once you know what "
                             ,
                           ";   abstraction you're designing and whether it is "
                             ,
                         ";   mutable or immutable, the next step is to design "
                             ,
                          ";   operations. What code do you want clients to be "
                             ,
                         ";   able to write? What operations need to be cheap? "
                             ,
                              ";                                               "
                             ,
                              ";   If you're not ready to write specifications "
                             ,
                         ";   directly, start with examples of client code you "
                             ,
                           ";   hope for. You can generalize an example into a "
                             ,
                           ";   specification by replacing each specific value "
                             ,
                              ";   with a variable that can take on any value. "
                             ,
                          ";   If your abstraction is immutable, the resulting "
                             ,
                        ";   specification might take the form of an algebraic "
                             ,
                              ";   law. Or you can use examples to create an   "
                             ,
                          ";   informal description of what an operation does, "
                             ,
                              ";   using the language of the abstraction. Such "
                             ,
                         ";   language might include phrases like ``add to the "
                             ,
                             ";   end of the sequence'' or ``take the smallest "
                             ,
                         ";   element from the bag.'' Good examples can evolve "
                             ,
                        ";   into specifications, and they also make good test "
                             ,
                              ";   cases.                                      "
                             ,
                              ";                                               "
                             ,
                   ";    • Completeness and testability. How many operations "
                             ,
                           ";   are enough? To know when an interface is done, "
                             ,
                             ";   I lean on the classification from \\         "
                             ,
                          ";   chaprefpagescheme.constructor-observer-mutator: "
                             ,
                             ";   A creator gives a new value of abstract type "
                             ,
                            ";   where we had none before. A producer takes an "
                             ,
                           ";   existing value of abstract type and gives us a "
                             ,
                            ";   new one. An observer can show a property of a "
                             ,
                        ";   value of abstract type, or even ``take it apart'' "
                             ,
                          ";   and give access to another value stored inside. "
                             ,
                          ";   And a mutator mutates a value of abstract type, "
                             ,
                              ";   provided the abstraction is mutable.        "
                             ,
                              ";                                               "
                             ,
                         ";   The same classification guides testing—because "
                             ,
                             ";   when you're testing an abstraction, external "
                             ,
                              ";   tests can't look at the representation.     "
                             ,
                           ";   In a world of abstraction, every test fits the "
                             ,
                           ";   same model: a call to a creator is followed by "
                             ,
                         ";   zero or more calls to producers and/or mutators, "
                             ,
                              ";   and finally by a call to an observer.       "
                             ,
                        ";     □ When an abstraction is immutable, there are "
                             ,
                         ";       no mutators, and so a test can be written as "
                             ,
                              ";       a single expression. The observer is    "
                             ,
                        ";       outermost, at the root of the abstract-syntax "
                             ,
                         ";       tree, and creators innermost, at or near the "
                             ,
                             ";       leaves. Such an expression can be placed "
                             ,
                              ";       directly in a [[check-expect]].         "
                             ,
                          ";     □ When an abstraction is mutable, there are "
                             ,
                           ";       mutators in play, and a typical test takes "
                             ,
                              ";       the form of a [[let]] binding (to name  "
                             ,
                        ";       created values that are to be mutated) with a "
                             ,
                          ";       sequence of expressions in the body. In the "
                             ,
                              ";       body, the last expression performs the  "
                             ,
                           ";       observation, and the preceding expressions "
                             ,
                        ";       mutate. Such a [[let]] expression can also be "
                             ,
                              ";       placed in a [[check-expect]].           "
                             ,
                              ";                                               "
                             ,
                        ";   These ideas not only help classify operations but "
                             ,
                            ";   also help judge when a design is complete and "
                             ,
                        ";   useful. If there is a producer that puts together "
                             ,
                              ";   a complex abstraction, but there is no      "
                             ,
                         ";   corresponding observer to take it apart, perhaps "
                             ,
                         ";   there is a problem. Similarly, if it is possible "
                             ,
                         ";   to mutate some part of an abstraction but not to "
                             ,
                         ";   observe it, programmers may not like the design. "
                             ,
                         ";   But if the interface makes it possible for every "
                             ,
                        ";   operation to be tested, there probably aren't any "
                             ,
                              ";   missing pieces.                             "
                             ,
                              ";                                               "
                             ,
                        ";    • Fit and finish. As you complete your design, "
                             ,
                          ";   sharpen your specification and your test suite. "
                             ,
                           ";   Abstract data types lend themselves especially "
                             ,
                        ";   well to specification by algebraic laws, as in \\ "
                             ,
                             ";   chaprefpagescheme.laws. If an abstraction is "
                             ,
                         ";   immutable, algebraic laws can be used to specify "
                             ,
                            ";   its operations directly. If an abstraction is "
                             ,
                           ";   mutable, algebraic laws can still be used, but "
                             ,
                         ";   now they specify relationships between the state "
                             ,
                         ";   of an object before and after a mutation. If you "
                             ,
                             ";   can specify how the result of one operations "
                             ,
                        ";   feeds into every other, and if you can turn these "
                             ,
                        ";   specifications into test cases, your design has a "
                             ,
                              ";   chance of being complete and coherent.      "
                             ,
                              ";                                               "
                             ,
                      ";  To illustrate these design tricks, I present what \\ "
                             ,
                       ";  java calls an [[ArrayList]]: a sequence abstraction "
                             ,
                         ";  that provides constant-time indexing but can also "
                             ,
                              ";  grow and shrink.                             "
                             ,
                              ";                                               "
                             ,
                       ";    • Description. The abstraction is a sequence of "
                             ,
                        ";   elements, each of type [[elem]]. The elements are "
                             ,
                             ";   numbered sequentially, and the number of the "
                             ,
                        ";   first element is part of the abstraction. I write "
                             ,
                     ";   the abstraction as \\arrayabsk \\vs, where \\vs is a "
                             ,
                            ";   sequence of values, and k is the index of the "
                             ,
                              ";   first value.                                "
                             ,
                     ";    • Mutability. A key goal is to update any element "
                             ,
                          ";   in constant time. That goal calls for a mutable "
                             ,
                              ";   abstraction.                                "
                             ,
                   ";    • Operations and cost model. In addition to classic "
                             ,
                         ";   array lookup and update ([[at]] and [[at-put]]), "
                             ,
                              ";   I also want the ability to add and remove   "
                             ,
                            ";   elements at either end, in constant amortized "
                             ,
                              ";   time.                                       "
                             ,
                              ";                                               "
                             ,
                         ";   I plan a single creator, operation [[new-from]], "
                             ,
                       ";   which takes one argument k and returns \\arrayabsk "
                             ,
                             ";   \\emptylist, the empty array starting at k.  "
                             ,
                              ";                                               "
                             ,
                        ";   I don't plan any producers; rather then produce a "
                             ,
                              ";   new array from an existing array, I plan to "
                             ,
                              ";   update arrays in place.                     "
                             ,
                              ";                                               "
                             ,
                             ";   As observers, I want not only to observe the "
                             ,
                           ";   element at any valid index but also to observe "
                             ,
                             ";   the low and high indices and the size of the "
                             ,
                        ";   array. Here are some algebraic laws: {mathpar} at "
                             ,
                           ";   (\\arrayabsk \\sconsv \\vs, k) = v             "
                             ,
                              ";                                               "
                             ,
                     ";   at(\\arrayabsk \\sconsv \\vs, k') = at(\\arrayabsk+1 "
                             ,
                             ";   \\vs, k'),  when k' !=k                      "
                             ,
                              ";                                               "
                             ,
                           ";   size(\\arrayabsk \\vs) = length(\\vs)          "
                             ,
                              ";                                               "
                             ,
                            ";   lo(\\arrayabsk \\vs) = k                      "
                             ,
                              ";                                               "
                             ,
                           ";   nexthi(\\arrayabsk \\vs) = k + length(\\vs)    "
                             ,
                              ";   {mathpar}                                   "
                             ,
                              ";                                               "
                             ,
                              ";   As mutators, I want not only the typical    "
                             ,
                              ";   [[at-put]], but also [[addlo]], [[remlo]],  "
                             ,
                              ";   [[addhi]], and [[remhi]]. Mutators can't be "
                             ,
                        ";   specified directly using algebraic laws, but here "
                             ,
                         ";   are some related algebraic laws: {mathpar} addlo "
                             ,
                    ";   (\\arrayabsk \\vs, v') = \\arrayabsk-1 \\sconsv' \\vs "
                             ,
                              ";                                               "
                             ,
                    ";   remlo_A(\\arrayabsk \\sconsv \\vs) = \\arrayabsk+1 \\ "
                             ,
                              ";   vs                                          "
                             ,
                              ";                                               "
                             ,
                           ";   remlo_V(\\arrayabsk \\sconsv \\vs) = v         "
                             ,
                              ";                                               "
                             ,
                    ";   atPut(\\arrayabsk \\sconsv \\vs, k, v') = \\arrayabsk "
                             ,
                            ";   \\sconsv' \\vs                                "
                             ,
                              ";                                               "
                             ,
                        ";   atPut(\\arrayabsk \\sconsv \\vs, k', v') = addlo( "
                             ,
                      ";   atPut(\\arrayabsk+1 \\vs, k', v'), v),  when k' !=k "
                             ,
                              ";   {mathpar}                                   "
                             ,
                      ";    • Completeness and testability. Every [[at-put]] "
                             ,
                              ";   can be observed by an [[at]]. Results of    "
                             ,
                         ";   [[addlo]] and [[remlo]] can be observed by their "
                             ,
                         ";   effects on [[lo]], as well as on [[size]] and on "
                             ,
                           ";   the relevant element. Similarly for [[addhi]]. "
                             ,
                        ";   Index k can be observed using [[lo]], and all of  "
                             ,
                             ";   \\vs can be observed by using [[at]] with an "
                             ,
                              ";   index i in the range lo <=i < nexthi.       "
                             ,
                     ";    • Fit and finish. To put the final touches on the "
                             ,
                        ";   specification, I might wish to specify a mutator. "
                             ,
                       ";   When an array A's current state is described by \\ "
                             ,
                      ";   arrayabsk \\sconsv \\vs, calling \\monobox(remlo A) "
                             ,
                        ";   returns v and mutates A such that its final state "
                             ,
                              ";   is described by remlo_V(A).                 "
                             ,
                              ";                                               "
                             ,
                             ";  \\stdbreak Here is the interface:[*]          "
                             ,
                              ";  <arraylist.mcl>=                             "
                             , "(module-type ARRAYLIST"
                             , "  (exports [abstype t]"
                             , "           [abstype elem]"
                             ,
"           [from   : (int -> t)]           ; creator (from index of first element)"
                             ,
                         "           [size   : (t -> int)]           ; observer"
                             ,
                         "           [at     : (t int -> elem)]      ; observer"
                             ,
                          "           [at-put : (t int elem -> unit)] ; mutator"
                             , ""
                             ,
                             "           [lo     : (t -> int)]       ; observer"
                             ,
                             "           [nexthi : (t -> int)]       ; observer"
                             ,
                              "           [addlo  : (t elem -> unit)] ; mutator"
                             ,
                              "           [addhi  : (t elem -> unit)] ; mutator"
                             ,
                              "           [remlo  : (t -> elem)]      ; mutator"
                             ,
                              "           [remhi  : (t -> elem)]))    ; mutator"
                             ,
                              ";  <arraylist.mcl>=                             "
                             , "(generic-module"
                             ,
        "   [ArrayList : ([Elem : (exports [abstype t])] --m-> (allof ARRAYLIST"
                             ,
"                                                               (exports [type elem Elem.t])))]"
                             , "   (module A (@m Array Elem))"
                             , "   (module U (@m UnsafeArray Elem))"
                             , "   (record-module Rep t ([elems : A.t]"
                             , "                         [low-index : int]"
                             , "                         [population : int]"
                             , "                         [low-stored : int]))"
                             , "   (type t Rep.t)"
                             , "   (type elem Elem.t)"
                             , ""
                             , "   (define t from ([i : int])"
                             , "     (Rep.make (U.new 3) i 0 0))"
                             , ""
                             ,
                             "   (define int size ([a : t]) (Rep.population a))"
                             , ""
                             , "   (define bool in-bounds? ([a : t] [i : int])"
                             , "     (if (>= i (Rep.low-index a))"
                             ,
                       "         (< (- i (Rep.low-index a)) (Rep.population a))"
                             , "         #f))"
                             , ""
                             ,
                             "   (define int internal-index ([a : t] [i : int])"
                             ,
                "     (let* ([k (+ (Rep.low-stored a) (- i (Rep.low-index a)))]"
                             ,
          "            [_ (when (< k 0) (error 'internal-error: 'array-index))]"
                             , "            [n (A.size (Rep.elems a))]"
                             , "            [idx (if (< k n) k (- k n))])"
                             , "       idx))"
                             , ""
                             , "   (define elem at ([a : t] [i : int])"
                             , "     (if (in-bounds? a i)"
                             ,
                            "         (A.at (Rep.elems a) (internal-index a i))"
                             , "         (error 'array-index-out-of-bounds)))"
                             , ""
                             ,
                         "   (define unit at-put ([a : t] [i : int] [v : elem])"
                             , "     (if (in-bounds? a i)"
                             ,
                      "         (A.at-put (Rep.elems a) (internal-index a i) v)"
                             , "         (error 'array-index-out-of-bounds)))"
                             , ""
                             ,
                         "   (define int lo     ([a : t]) (Rep.low-index a))   "
                             ,
     "   (define int nexthi ([a : t]) (+ (Rep.low-index a) (Rep.population a)))"
                             , ""
                             , "   (define unit maybe-grow ([a : t])"
                             , "     (when (>= (size a) (A.size (Rep.elems a)))"
                             , "       (let* ([n  (A.size (Rep.elems a))]"
                             ,
                             "              [n' (if (Int.= n 0) 8 (Int.* 2 n))]"
                             , "              [new-elems (U.new n')]"
                             , "              [start (lo a)]"
                             , "              [limit (nexthi a)]"
                             , "              [i 0]"
                             ,
              "              [_ (while (< start limit)      ; copy the elements"
                             ,
                        "                   (A.at-put new-elems i (at a start))"
                             , "                   (set i (+ i 1))"
                             , "                   (set start (+ start 1)))])"
                             , "         (Rep.set-elems! a new-elems)"
                             , "         (Rep.set-low-stored! a 0))))"
                             , ""
                             , "   (define unit addhi ([a : t] [v : elem])"
                             , "     (maybe-grow a)"
                             , "     (let ([i (nexthi a)])"
                             ,
                      "        (Rep.set-population! a (+ (Rep.population a) 1))"
                             , "        (at-put a i v)))"
                             , "     "
                             , "   (define unit addlo ([a : t] [v : elem])"
                             , "     (maybe-grow a)"
                             ,
                         "     (Rep.set-population! a (+ (Rep.population a) 1))"
                             ,
                         "     (Rep.set-low-index!  a (- (Rep.low-index a)  1))"
                             ,
                         "     (Rep.set-low-stored! a (- (Rep.low-stored a) 1))"
                             , "     (when (< (Rep.low-stored a) 0)"
                             ,
 "       (Rep.set-low-stored! a (+ (Rep.low-stored a) (A.size (Rep.elems a)))))"
                             , "     (at-put a (Rep.low-index a) v))"
                             , "     "
                             , "   (define elem remhi ([a : t])"
                             , "     (if (<= (Rep.population a) 0)"
                             , "         (error 'removal-from-empty-array)"
                             , "         (let* ([v (at a (- (nexthi a) 1))]"
                             ,
         "                [_ (Rep.set-population! a (- (Rep.population a) 1))])"
                             , "           v)))"
                             , ""
                             , "   (define elem remlo ([a : t])"
                             , "     (if (<= (Rep.population a) 0)"
                             , "         (error 'removal-from-empty-array)"
                             , "         (let* ([v (at a (lo a))]"
                             ,
          "                [_ (Rep.set-population! a (- (Rep.population a) 1))]"
                             ,
                       "                [_ (Rep.set-low-index! a (+ (lo a) 1))]"
                             ,
          "                [_ (Rep.set-low-stored! a (+ (Rep.low-stored a) 1))]"
                             ,
    "                [_ (when (Int.= (Rep.low-stored a) (A.size (Rep.elems a)))"
                             ,
                           "                       (Rep.set-low-stored! a 0))])"
                             , "           v)))"
                             , ""
                             , ""
                             , "   (define unit setlo ([a : t] [i : int])"
                             , "     (Rep.set-low-index! a i))"
                             , ""
                             , ")"
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             ,
                          "(define bool and ([b : bool] [c : bool]) (if b c b))"
                             ,
                          "(define bool or  ([b : bool] [c : bool]) (if b b c))"
                             ,
              "(define bool not ([b : bool])            (if b (= 1 0) (= 0 0)))"
                             ,
                    "(define int mod ([m : int] [n : int]) (- m (* n (/ m n))))"
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             , "(generic-module"
                             , "   [Array : ([M : (exports (abstype t))] --m-> "
                             ,
                     "                (allof ARRAY (exports (type elem M.t))))]"
                             , "   (module A (@m ArrayCore M))"
                             , "   (type t A.t)"
                             , "   (type elem M.t)"
                             , "   (val new A.new)"
                             , "   (val empty A.empty)"
                             , "   (val at A.at)"
                             , "   (val size A.size)"
                             , "   (val at-put A.at-put))"
                             ,
                      ";  <predefined Molecule types, functions, and modules>= "
                             , "(generic-module"
                             , "   [Ref : ([M : (exports (abstype t))] --m->"
                             , "                  (exports [abstype t]"
                             , "                           [new : (M.t -> t)]"
                             , "                           [!   : (t -> M.t)]"
                             ,
                         "                           [:=  : (t M.t -> unit)]))]"
                             , "  (module A (@m ArrayCore M))"
                             , "  (type t A.t)"
                             , "  (define t    new ([x : M.t])  (A.new 1 x))"
                             , "  (define M.t  !   ([cell : t]) (A.at cell 0))"
                             ,
               "  (define unit :=  ([cell : t] [x : M.t]) (A.at-put cell 0 x)))"
                              ] 
      val xdefs = stringsxdefs ("built-in types", predefinedTypes)
  in  readEvalPrintWith predefinedFunctionError (xdefs, initialBasis,
                                                                 noninteractive)
  end

val options = case OS.Process.getEnv "BPCOPTIONS" of SOME s => ":" ^ s ^ ":" |
                                                                      NONE => ""
val () =
  if String.isSubstring ":basis:" options then
    let fun show (x, c) = app print [whatdec c, " ", x, "\n"]
    in  app show (fst initialBasis)
    end
  else
    ()


(*****************************************************************)
(*                                                               *)
(*   FUNCTION [[RUNAS]], WHICH EVALUATES STANDARD INPUT GIVEN [[INITIALBASIS]] *)
(*                                                               *)
(*****************************************************************)

(* <function [[runAs]], which evaluates standard input given [[initialBasis]]>= *)
fun runAs interactivity = 
  let val _ = setup_error_format interactivity
      val prompts = if prompts interactivity then stdPrompts else noPrompts
      val xdefs = filexdefs ("standard input", TextIO.stdIn, prompts)
  in  ignore (readEvalPrintWith eprintln (xdefs, initialBasis, interactivity))
  end 
(* Utility function for limiting the depth of recursion *)
(*                                              *)
(* If there's no other overhead, MLton delivers *)
(* 25 million evals per second. Finding all solutions to *)
(* a Boolean formula requires on the order of 200. *)
(* <boxed values 27>=                           *)
val _ = op runAs : interactivity -> unit


(*****************************************************************)
(*                                                               *)
(*   CODE THAT LOOKS AT COMMAND-LINE ARGUMENTS AND CALLS [[RUNAS]] TO RUN THE INTERPRETER *)
(*                                                               *)
(*****************************************************************)

(* To launch the interpreter, I look at command-line *)
(* arguments and call [[runAs]]. The code is executed *)
(* only for its side effect, so I put it on the *)
(* right-hand side of a [[val]] binding with no name. *)
(* Function [[CommandLine.arguments]] returns an *)
(* argument list; [[CommandLine.name]] returns the name *)
(* by which the interpreter was invoked.        *)
(* <code that looks at command-line arguments and calls [[runAs]] to run the interpreter>= *)
val _ = case CommandLine.arguments ()
          of []     => runAs (PROMPTING,     PRINTING)
           | ["-q"] => runAs (NOT_PROMPTING, PRINTING)
           | ["-qq"]=> runAs (NOT_PROMPTING, NOT_PRINTING)   (*OMIT*)
           | ["-names"]=> dump_names initialBasis (*OMIT*)
           | _      => eprintln ("Usage: " ^ CommandLine.name () ^ " [-q]")
