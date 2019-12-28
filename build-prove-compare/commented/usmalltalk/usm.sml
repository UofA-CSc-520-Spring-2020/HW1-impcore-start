(* The code in the interpreter is organized so that the *)
(* [[<<support for bootstrapping classes and values used *)
(* during parsing>>]] is as early as possible,  *)
(* immediately following the definition of [[<<abstract *)
(* syntax and values for uSmalltalk>>]] and the *)
(* associated utility functions. Afterward come parsing, *)
(* primitives, and evaluation. The code for     *)
(* [[<<implementations of uSmalltalk primitives and *)
(* definition of [[initialBasis]]>>]] comes almost at *)
(* the end, just before the execution of the command *)
(* line. The full structure of the interpreter resembles *)
(* the structure of the micro-Scheme interpreter shown *)
(* in \chunkrefmlscheme.chunk.mlscheme.sml, with the *)
(* addition of chunks for bootstrapping and for stack *)
(* tracing.                                     *)
(*                                              *)
(* <usm.sml>=                                   *)


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
(* <boxed values 120>=                          *)
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
(* <boxed values 16>=                           *)
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
(* <boxed values 34>=                           *)
val _ = op duplicatename : name list -> name option
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
(* <boxed values 35>=                           *)
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
(* <boxed values 79>=                           *)
val _ = op intString : int -> string
(* Lists! Functions [[spaceSep]] and [[commaSep]] are *)
(* special cases of the more general function   *)
(* [[separate]].                                *)
(* <boxed values 79>=                           *)
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
(* <boxed values 80>=                           *)
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
(* <boxed values 84>=                           *)
val _ = op zip3   : 'a list * 'b list * 'c list -> ('a * 'b * 'c) list
val _ = op unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
(* <boxed values 84>=                           *)
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
(* <boxed values 84>=                           *)
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
(* <boxed values 85>=                           *)
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
(* <boxed values 86>=                           *)
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
(* <boxed values 36>=                           *)
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
(* <boxed values 81>=                           *)
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
(* <boxed values 82>=                           *)
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
(* <boxed values 83>=                           *)
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
(* <boxed values 92>=                           *)
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
(* <boxed values 93>=                           *)
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
(* <boxed values 94>=                           *)
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
(* <boxed values 94>=                           *)
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
(* <boxed values 95>=                           *)
val _ = op listOfStream : 'a stream -> 'a list
(* The more interesting streams are those that result *)
(* from actions. To help create such streams, I define *)
(* [[delayedStream]] as a convenience abbreviation for *)
(* creating a stream from one action.           *)
(* <boxed values 95>=                           *)
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
(* <boxed values 96>=                           *)
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
(* <boxed values 97>=                           *)
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
(* <boxed values 98>=                           *)
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
(* <boxed values 99>=                           *)
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
(* <boxed values 100>=                          *)
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
(* <boxed values 101>=                          *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <boxed values 101>=                          *)
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
(* <boxed values 102>=                          *)
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
(* <boxed values 103>=                          *)
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
(* <boxed values 104>=                          *)
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
(* <boxed values 105>=                          *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* Concatenation turns a stream of streams of A's into a *)
(* single stream of A's. I define it using a    *)
(* [[streamOfUnfold]] with a two-part state: the first *)
(* element of the state holds an initial [[xs]], and the *)
(* second part holds the stream of all remaining *)
(* streams, [[xss]]. To concatenate the stream of *)
(* streams [[xss]], I use an initial state of [[(EOS, *)
(* xss)]].                                      *)
(* <boxed values 105>=                          *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* <streams>=                                   *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* The composition of [[concat]] with [[map f]] is very *)
(* common in list and stream processing, so I give it a *)
(* name.                                        *)
(* <boxed values 106>=                          *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* <streams>=                                   *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* The code used to append two streams is much like the *)
(* code used to concatenate arbitrarily many streams. *)
(* To avoid duplicating the tricky manipulation of *)
(* states, I simply implement append using      *)
(* concatenation.                               *)
(* <boxed values 107>=                          *)
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
(* <boxed values 108>=                          *)
val _ = op streamTake : int * 'a stream -> 'a list
(* <streams>=                                   *)
fun streamDrop (0, xs) = xs
  | streamDrop (n, xs) =
      case streamGet xs
        of SOME (_, xs) => streamDrop (n-1, xs)
         | NONE => EOS
(* If I want ``take,'' sooner or later I'm sure to want *)
(* ``drop'' (\chunkrefmlinterps.chunk.use-streamDrop). *)
(* <boxed values 109>=                          *)
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
(* <boxed values 116>=                          *)
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
(* <boxed values 117>=                          *)
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
(* <boxed values 118>=                          *)
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
(* <boxed values 119>=                          *)
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
(* <boxed values 121>=                          *)
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
(* <boxed values 122>=                          *)
val _ = op pzero : ('a, 'b) xformer
(* <boxed values 122>=                          *)
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
(* <boxed values 123>=                          *)
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
(* <boxed values 124>=                          *)
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
(* <boxed values 125>=                          *)
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
(* <boxed values 126>=                          *)
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
(* <boxed values 127>=                          *)
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
(* <boxed values 128>=                          *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* <stream transformers and their combinators>= *)
fun eqx y = 
  sat (fn y' => y = y') 
(* Transformer [[eqx b]] is [[sat]] specialized to an *)
(* equality predicate. It is typically used to recognize *)
(* special characters like keywords and minus signs. *)
(* <boxed values 129>=                          *)
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
(* <boxed values 130>=                          *)
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
(* <boxed values 131>=                          *)
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
(* <boxed values 132>=                          *)
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
(* <boxed values 133>=                          *)
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
(* <boxed values 134>=                          *)
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
(* <boxed values 135>=                          *)
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
(* <boxed values 136>=                          *)
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
(* <boxed values 111>=                          *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* To keep track of the source location of a line, *)
(* token, expression, or other datum, I put the location *)
(* and the datum together in a pair. To make it easier *)
(* to read the types, I define a type abbreviation which *)
(* says that a value paired with a location is  *)
(* ``located.''                                 *)
(* <boxed values 111>=                          *)
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
(* To raise the [[Located]] exception, we use function *)
(* [[atLoc]]. Calling \monoboxatLoc f x applies [[f]] *)
(* to [[x]] within the scope of handlers that convert *)
(* recognized exceptions to the [[Located]] exception: *)
(* <boxed values 112>=                          *)
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
(* <boxed values 113>=                          *)
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
(* <boxed values 114>=                          *)
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
(* <boxed values 115>=                          *)
val _ = op errorAt : string -> srcloc -> 'a error
(* All locations originate in a located stream of lines. *)
(* The locations share a filename, and the line numbers *)
(* are 1, 2, 3, ... and so on. [*]              *)
(* <boxed values 115>=                          *)
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
(* <boxed values 144>=                          *)
type 'a eol_marked = 'a eol_marked
val _ = op drainLine : 'a eol_marked stream -> 'a eol_marked stream
(* <boxed values 144>=                          *)
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
(* <boxed values 137>=                          *)
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
(* <boxed values 138>=                          *)
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
(* <boxed values 139>=                          *)
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
(* <boxed values 140>=                          *)
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
(* <boxed values 141>=                          *)
val _ = op intFromChars : char list -> int error
(* <support for lexical analysis>=              *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* In this book, every language except uProlog can use *)
(* [[intToken]].                                *)
(* <boxed values 142>=                          *)
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
(* <boxed values 143>=                          *)
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
(* <boxed values 145>=                          *)
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
(* <boxed values 146>=                          *)
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
(* <boxed values 147>=                          *)
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
(* <boxed values 148>=                          *)
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
(* <boxed values 152>=                          *)
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
(* <boxed values 149>=                          *)
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
(* <boxed values 150>=                          *)
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
(* <boxed values 151>=                          *)
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
(* <boxed values 153>=                          *)
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
(* <boxed values 154>=                          *)
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
(* <boxed values 155>=                          *)
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
(* <boxed values 156>=                          *)
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
(* <boxed values 157>=                          *)
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
(* <boxed values 158>=                          *)
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
(* <boxed values 159>=                          *)
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
(* <boxed values 160>=                          *)
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
(* <boxed values 161>=                          *)
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
(*   ABSTRACT SYNTAX AND VALUES FOR \USMALLTALK                  *)
(*                                                               *)
(*****************************************************************)

(* Interpreter things                           *)
(*                                              *)
(* Support for abstract syntax and values is pulled *)
(* together in the same way as in the other     *)
(* interpreters. But in uSmalltalk, both [[valueString]] *)
(* and [[expString]] use the [[className]] utility *)
(* function, which I define here.               *)
(* <abstract syntax and values for \usmalltalk>= *)
(* Stack frames                                 *)
(*                                              *)
(* <support for \usmalltalk\ stack frames>=     *)
datatype frame = FN of int
local
  val next_f = ref 0
in
  fun newFrame () = FN (!next_f) before next_f := !next_f + 1
end

type active_send = { method : name, class : name, loc : srcloc }

val noFrame = newFrame () (* top level, unit tests, etc... *)

fun activeSendString { method, class, loc = (file, line) } =
  let val obj = if String.isPrefix "class " class then class
                else "an object of class " ^ class
  in  concat [file, ", line ", intString line, ": ", "sent '", method, "' to ",
                                                                            obj]
  end

fun raString (FN n) = "F@-" ^ intString n
(* The [[rep]] part of an object exposes one of the *)
(* biggest differences between uSmalltalk and   *)
(* Smalltalk-80. In Smalltalk-80, every object owns a *)
(* collection of mutable locations, called ``instance *)
(* variables,'' each of which can be filled either with *)
(* an ordinary object or with a sequence of bytes. But *)
(* because uSmalltalk is implemented in ML, it doesn't *)
(* work with byte sequences; an object's representation *)
(* is defined by an ML datatype. In uSmalltalk, that *)
(* datatype can identify an ordinary, user-defined *)
(* object, which is represented by a collection of named *)
(* locations. Or it can identify an array, a number, *)
(* a symbol, a closure, a class object, or a compiled *)
(* method:                                      *)
(* <definitions of [[exp]], [[rep]], and [[class]] for \usmalltalk>= *)
datatype rep = USER     of value ref env (* ordinary object *)
             | ARRAY    of value Array.array
             | NUM      of int
             | SYM      of name
             | CLOSURE  of name list * exp list * value ref env * class * frame
             | CLASSREP of class
             | METHOD   of method
(* Internally, an object's class is represented by an ML *)
(* value of type [[class]]. Its internal representation *)
(* includes a superclass, instance-variable names, and *)
(* methods. Except for the distinguished root class, *)
(* [[Object]], every class has a superclass. A class's *)
(* [[ivars]] and [[methods]] lists include only the *)
(* instance variables and methods defined in that class, *)
(* not those of its superclass.                 *)
(* <definitions of [[exp]], [[rep]], and [[class]] for \usmalltalk>= *)
and class  = CLASS of { name    : name            (* name of the class *)
                      , super   : class option    (* superclass, if any *)
                      , ivars   : string list     (* instance variables *)
                      , methods : method env ref
                                                 (* both exported and private *)
                      , class   : metaclass ref
                                                 (* class of the class object *)
                      }
and metaclass = META of class | PENDING
(* The [[LITERAL]] form alone isn't enough: there are *)
(* places in the interpreter—for example, the *)
(* read-eval-print loop—where I must send a message to *)
(* an object, which has both [[class]] and [[rep]]. *)
(* To form an expression from such an object, I use  *)
(* [[VALUE]].                                   *)
(* <definitions of [[exp]], [[rep]], and [[class]] for \usmalltalk>= *)
and exp = VAR       of name
        | SET       of name * exp
        | SEND      of srcloc * exp * name * exp list
        | BEGIN     of exp list
        | BLOCK     of name list * exp list
        | RETURN    of exp
        | PRIMITIVE of name * exp list
        | SUPER
        | LITERAL   of rep
        | VALUE     of class * rep
(* Although we usually use the word ``object,'' the *)
(* ML type of the thing that [[eval]] returns is *)
(* [[value]], just as in every other interpreter in this *)
(* book. An object is represented in two parts: its *)
(* class, which determines its response to messages, and *)
(* its internal representation, which has ML type *)
(* [[rep]].                                     *)
(* <definitions of [[value]] and [[method]] for \usmalltalk>= *)
withtype value = class * rep
(* A method has a name, formal parameters, local *)
(* variables, and a body. A method also stores the *)
(* superclass of the class in which it is defined, which *)
(* it uses to interpret messages sent to [[super]]. *)
(* <definitions of [[value]] and [[method]] for \usmalltalk>= *)
and method = { name : name, formals : name list, locals : name list, body : exp
             , superclass : class (* used to send messages to super *)
             }

(* Abstract syntax                              *)
(*                                              *)
(* The syntax of definitions doesn't require any long *)
(* explanations, so I begin with [[def]]. A definition *)
(* may be one of our old friends [[VAL]] and [[EXP]], a *)
(* block definition ([[DEFINE]]), or a class definition *)
(* ([[CLASSD]]). A class definition may include both *)
(* instance methods and class methods.          *)
(* <definition of [[def]] for \usmalltalk>=     *)
datatype def = VAL    of name * exp
             | EXP    of exp
             | DEFINE of name * name list * exp
             | CLASSD of { name    : string
                         , super   : string
                         , ivars   : string list
                         , methods : method_def list
                         }
and method_flavor = IMETHOD          (* instance method *)
                  | CMETHOD          (* class method    *)
  withtype method_def = { flavor : method_flavor, name : name
                        , formals : name list, locals : name list, body : exp 
                        }
(* <definition of [[unit_test]] for \usmalltalk>= *)
(* <definition of [[unit_test]] for untyped languages (shared)>= *)
datatype unit_test = CHECK_EXPECT of exp * exp
                   | CHECK_ASSERT of exp
                   | CHECK_ERROR  of exp
             | CHECK_PRINT of exp * string
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
fun className (CLASS {name, ...}) = name
(* To avoid confusion, tracing code typically avoids *)
(* [[print]] methods; instead, it uses [[valueString]] *)
(* to give information about a value.           *)
(* <definition of [[valueString]] for \usmalltalk>= *)
fun valueString (c, NUM n) = intString n ^ valueString(c, USER [])
  | valueString (_, SYM v) = v
  | valueString (c, _) = "<" ^ className c ^ ">"
(* <definition of [[expString]] for \usmalltalk>= *)
fun expString e =
  let fun bracket s = "(" ^ s ^ ")"
      val bracketSpace = bracket o spaceSep
      fun exps es = map expString es
      fun symString x = x
      fun valueString (_, NUM n) = intString n
        | valueString (_, SYM x) = "'" ^ symString x
        | valueString (c, _) = "<" ^ className c ^ ">"
  in  case e
        of LITERAL (NUM n) => intString n
         | LITERAL (SYM n) => "'" ^ symString n
         | LITERAL _ => "<wildly unexpected literal>"
         | VAR name => name
         | SET (x, e) => bracketSpace ["set", x, expString e]
         | RETURN e   => bracketSpace ["return", expString e]
         | SEND (_, e, msg, es) => bracketSpace (expString e :: msg :: exps es)
         | BEGIN es => bracketSpace ("begin" :: exps es)
         | PRIMITIVE (p, es) => bracketSpace ("primitive" :: p :: exps es)
         | BLOCK ([], es) => "[" ^ spaceSep (exps es) ^ "]"
         | BLOCK (xs, es) => bracketSpace ["block", bracketSpace xs,
                                           spaceSep (exps es)]
         | VALUE v => valueString v
         | SUPER => "super"
  end


(*****************************************************************)
(*                                                               *)
(*   SUPPORT FOR LOGGING (FOR COVERAGE ANALYSIS)                 *)
(*                                                               *)
(*****************************************************************)

(* <support for logging (for coverage analysis)>= *)
val logging =
  String.isSubstring ":log:" (":" ^ getOpt (OS.Process.getEnv "BPCOPTIONS", "")
                                                                          ^ ":")
fun q s = "\"" ^ s ^ "\""
val _ = if logging then println "val ops = ...\n" else ()

fun logSend srcloc msgname =
  app print [ "\nops.SEND { loc = ", q (srclocString srcloc)
            , ", selector = ", q msgname, " }\n" ]
fun logFind name candidate =
  app print ["\nops.findMethod { selector = ", q name
              , ", on = ", q (className candidate), "}\n"]

fun logClass name (ms : method list) =
  let fun subclassExp (SEND (_, _, "subclassResponsibility", _)) = true
        | subclassExp (BEGIN [e]) = subclassExp e
        | subclassExp _ = false
      val subclassM = subclassExp o #body
      val methodNames = commaSep o map (q o #name)
  in  app print [ "\nops.class { name = ", q name, ", methods = { " ,
                                                                  methodNames ms
                , " }, subclass_responsibilities = { "
                , methodNames (List.filter subclassM ms), " } }\n"
                ]
  end

fun logGetMethod class m =
  app print ["\nops.getMethod { class = ", q class, ", method = ", q m, " }\n"]

fun logSetMethod class m =
  app print ["\nops.setMethod { class = ", q class, ", method = ", q m, " }\n"]


(*****************************************************************)
(*                                                               *)
(*   UTILITY FUNCTIONS ON \USMALLTALK\ CLASSES, METHODS, AND VALUES *)
(*                                                               *)
(*****************************************************************)

(* <utility functions on \usmalltalk\ classes, methods, and values>= *)
fun instanceVars (_, USER rep) = rep
  | instanceVars self = bind ("self", ref self, emptyEnv)
(* A regrettable consequence of this design is that an *)
(* object with a primitive representation has no *)
(* instance variables besides [[self]]. \stdbreak *)
(* By contrast, an object with a [[USER]] representation *)
(* has as many instance variables as are dictated by its *)
(* class's definition—always including an instance *)
(* variable [[self]], which is inherited from class *)
(* [[Object]].                                  *)
(* <boxed values 1>=                            *)
val _ = op instanceVars : value -> value ref env
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <utility functions on \usmalltalk\ classes, methods, and values>= *)
fun valueSelector [] = "value"
  | valueSelector args = concat (map (fn _ => "value:") args)
(* <utility functions on \usmalltalk\ classes, methods, and values>= *)
fun className (CLASS {name,  ...}) = name
fun classId   (CLASS {class, ...}) = class
(* Utilities for manipulating classes           *)
(*                                              *)
(* Because a class can point to its superclass, the type *)
(* [[class]] has to be a recursive type implemented as *)
(* an ML [[datatype]]. To get access to information *)
(* about a class, we have to write a pattern match. When *)
(* all we want is a class's name or its unique  *)
(* identifier, pattern matching is fairly heavy *)
(* notation, so I provide two convenience functions. *)
(* The ``[[...]]'' notation in each pattern match tells *)
(* the Standard ML compiler that not all fields of the *)
(* record in curly braces are mentioned, and the ones *)
(* not mentioned should be ignored.             *)
(* <boxed values 58>=                           *)
val _ = op className : class -> name
val _ = op classId   : class -> metaclass ref
(* The [[xdeftable]] is shared with the Impcore parser. *)
(* Function [[reduce_to_xdef]] is almost shareable as *)
(* well, but not quite---the abstract syntax of *)
(* [[DEFINE]] is different.                     *)

(* <utility functions on \usmalltalk\ classes, methods, and values>= *)
fun methodName ({ name, ... } : method) = name
fun methodsEnv ms = foldl (fn (m, rho) => bind (methodName m, m, rho)) emptyEnv
                                                                              ms
(* We extract a name from a method using another *)
(* convenience function, [[methodName]]. Other  *)
(* manipulations of methods include [[renameMethod]], *)
(* which is used when a user class wants to use a *)
(* primitive method with a name other than the one *)
(* I built in, and [[methods]], which builds an *)
(* environment suitable for use in a class.     *)
(* <boxed values 59>=                           *)
val _ = op methodName   : method -> name
val _ = op methodsEnv   : method list -> method env
(* <utility functions on \usmalltalk\ classes, methods, and values>= *)
fun mkClass name meta super ivars ms =
  (
(* <if any name in [[ivars]] repeats a name declared in a superclass, raise [[RuntimeError]]>= *)
    let fun checkDuplicateIvar (SOME (CLASS { name = c', ivars, super, ... })) x
                                                                               =
            if member x ivars then
              raise RuntimeError ("Instance variable " ^ x ^ " of class " ^ name
                                                                               ^
                                  " duplicates a variable of superclass " ^ c')
            else
              checkDuplicateIvar super x
        | checkDuplicateIvar NONE x = ()
    in  app (checkDuplicateIvar (SOME super)) ivars
    end
  ; if logging then logClass name ms else () (*OMIT*)
  ; CLASS { name = name, super = SOME super, ivars = ivars
          , methods = ref (methodsEnv ms), class = ref meta }
  )
(* In general, I make a new class by calling    *)
(* [[mkClass]], which checks to be sure that no instance *)
(* variable is repeated. Each class is uniquely *)
(* identified by its [[class]] field, which points to a *)
(* unique mutable location.                     *)
(* <boxed values 60>=                           *)
val _ = op mkClass : name -> metaclass -> class -> name list -> method list ->
                                                                           class
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)




(*****************************************************************)
(*                                                               *)
(*   SUPPORT FOR BOOTSTRAPPING CLASSES AND VALUES USED DURING PARSING *)
(*                                                               *)
(*****************************************************************)

(* <support for bootstrapping classes and values used during parsing>= *)
local 
  val intClass    = ref NONE : class option ref
  val symbolClass = ref NONE : class option ref
  val arrayClass  = ref NONE : class option ref
  fun badlit what = 
    raise InternalError
        ("(bootstrapping) -- cannot " ^ what ^ " anywhere in predefined classes"
                                                                               )
in
  fun mkInteger n = (valOf (!intClass), NUM n)
    handle Option => badlit "evaluate integer literal or use array literal"
  
  fun mkSymbol s = (valOf (!symbolClass), SYM s)
    handle Option => badlit "evaluate symbol literal or use array literal"
  
  fun mkArray a = (valOf (!arrayClass), ARRAY (Array.fromList a))
    handle Option => badlit "use array literal"
(* Because it's hard to reason about reference cells, *)
(* I define them inside ML's [[local]] form. This form *)
(* protects the reference cells from outside    *)
(* interference: the only functions whose behavior can *)
(* depend on the contents of the reference cells are *)
(* defined between [[local]] and [[end]].       *)
(* <boxed values 11>=                           *)
val _ = op mkInteger : int        -> value
val _ = op mkSymbol  : string     -> value
val _ = op mkArray   : value list -> value
(* [*]                                          *)

(* Function [[valOf]] and exception [[Option]] are part *)
(* of the initial basis of Standard ML.         *)
(*                                              *)
(* \penalty-800                                 *)
(*                                              *)

(* <support for bootstrapping classes and values used during parsing>= *)
  fun findClass (name, xi) =
        case !(find (name, xi))
          of (_, CLASSREP c) => c
           | _ => raise InternalError ("class " ^ name ^ " is'nt defined")
  fun saveLiteralClasses xi =
    ( intClass    := SOME (findClass ("SmallInteger", xi))
    ; symbolClass := SOME (findClass ("Symbol",       xi))
    ; arrayClass  := SOME (findClass ("Array",        xi))
    )
end
(* Once uSmalltalk's predefined class definitions have *)
(* been read, my initialization code calls function *)
(* [[saveLiteralClasses]] to store the appropriate *)
(* classes in the reference cells. The environment *)
(* containing the initial basis is passed as the *)
(* parameter [[xi]].                            *)
(* <boxed values 12>=                           *)
val _ = op findClass : string * value ref env -> class
(* [*]                                          *)

(* <support for bootstrapping classes and values used during parsing>= *)
local
  val trueValue  = ref NONE : value option ref
  val falseValue = ref NONE : value option ref
in
  fun mkBoolean b = valOf (!(if b then trueValue else falseValue))
    handle Option => raise InternalError "uninitialized Booleans"
  fun saveTrueAndFalse xi =
    ( trueValue  := SOME (!(find ("true",  xi)))
    ; falseValue := SOME (!(find ("false", xi)))
    )
end
(* Booleans                                     *)
(*                                              *)
(* I use the same technique for Booleans, except instead *)
(* of using a mutable cell for each class, I use a *)
(* mutable cell for each value.                 *)
(* <boxed values 14>=                           *)
val _ = op mkBoolean : bool -> value
(* <support for bootstrapping classes and values used during parsing>= *)
local
  val blockClass = ref NONE : class option ref
in
  fun mkBlock c = (valOf (!blockClass), CLOSURE c)
    handle Option => 
        raise InternalError 
            "Bad blockClass; evaluated block expression in predefined classes?"
  fun saveBlockClass xi =
    blockClass := SOME (findClass ("Block", xi))
end
(* Bootstrapping                                *)
(*                                              *)
(* Blocks                                       *)
(*                                              *)
(* I use the technique again for blocks. I could *)
(* actually get away without bootstrapping the [[Block]] *)
(* class, but by defining [[Block]] and [[Boolean]] *)
(* together, I clarify their relationship, especially *)
(* the implementations of the [[whileTrue:]] and *)
(* [[whileFalse:]] methods.                     *)
(* <boxed values 63>=                           *)
val _ = op mkBlock : name list * exp list * value ref env * class * frame ->
                                                                           value
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <support for bootstrapping classes and values used during parsing>= *)
local
  val compiledMethodClass = ref NONE : class option ref
in
  fun mkCompiledMethod m = (valOf (!compiledMethodClass), METHOD m)
    handle Option => 
      raise InternalError "Bad compiledMethodClass"
  fun saveCompiledMethodClass xi =
    compiledMethodClass := SOME (findClass ("CompiledMethod", xi))
end



(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS AND PARSING FOR \USMALLTALK, PROVIDING [[FILEXDEFS]] AND [[STRINGSXDEFS]] *)
(*                                                               *)
(*****************************************************************)

(* Lexing and parsing                           *)
(*                                              *)
(* <lexical analysis and parsing for \usmalltalk, providing [[filexdefs]] and [[stringsxdefs]]>= *)
(* A source-code location includes a name for the *)
(* source, plus line number.                    *)
(* <lexical analysis for \usmalltalk>=          *)
val nullsrc : srcloc = ("internally generated SEND node", 1)
(* The representation of a token is almost the same as *)
(* in micro-Scheme. The differences are that there are *)
(* two kinds of brackets, and that a [[#]] character *)
(* does not introduce a Boolean.                *)
(* <lexical analysis for \usmalltalk>=          *)
datatype pretoken = INTCHARS of char list
                  | NAME     of name
                  | QUOTE    of string option (* symbol or array *)
type token = pretoken plus_brackets
(* To produce error messages, we must be able to convert *)
(* a token back to a string.                    *)
(* <lexical analysis for \usmalltalk>=          *)
fun pretokenString (INTCHARS ds)    = implode ds
  | pretokenString (NAME    x)      = x
  | pretokenString (QUOTE NONE)     = "'"
  | pretokenString (QUOTE (SOME s)) = "'" ^ s
(* <lexical analysis for \usmalltalk>=          *)
local
  val nondelims = many1 (sat (not o isDelim) one)

  fun validate NONE = NONE (* end of line *)
    | validate (SOME (#";", cs)) = NONE (* comment *)
    | validate (SOME (c, cs)) = 
        let val msg = "invalid initial character in `" ^
                      implode (c::listOfStream cs) ^ "'"
        in  SOME (ERROR msg, EOS) : (pretoken error * char stream) option
        end
in
  val smalltalkToken =
    whitespace *> bracketLexer (
            (QUOTE o SOME o implode) <$> (eqx #"'" one *> nondelims)
        <|> QUOTE NONE               <$  eqx #"'" one
        <|> INTCHARS                 <$> intChars isDelim   
        <|> (NAME o implode)         <$> nondelims                          
        <|> (validate o streamGet)
        )
(* <boxed values 70>=                           *)
val _ = op smalltalkToken : token lexer
end
(* <parsers for single \usmalltalk\ tokens>=    *)
type 'a parser = (token, 'a) polyparser
val token : token parser = token (* make it monomorphic *)
val pretoken  = (fn (PRETOKEN t)=> SOME t  | _ => NONE) <$>? token
val name = (fn (NAME s)         => SOME s  | _ => NONE) <$>? pretoken
val intchars = (fn (INTCHARS ds)=> SOME ds | _ => NONE) <$>? pretoken
val sym  = (fn (QUOTE (SOME s)) => SOME s  | _ => NONE) <$>? pretoken
val quote= (fn (QUOTE NONE    ) => SOME () | _ => NONE) <$>? pretoken
val any_name = name

val int = intFromChars <$>! intchars

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
(* <boxed values 45>=                           *)
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
(* <boxed values 46>=                           *)
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
(* <boxed values 47>=                           *)
val _ = op kw : string -> string parser
val _ = op usageParsers : (string * 'a parser) list -> 'a parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* Parsing                                      *)
(*                                              *)
(* Smalltalk has simple rules for computing the arity of *)
(* a message based on the message's name: if the name is *)
(* symbolic, the message is binary (one receiver, one *)
(* argument); if the name is alphanumeric, the number of *)
(* arguments is the number of colons. Unfortunately, in *)
(* uSmalltalk a name can mix alphanumerics and symbols. *)
(* To decide the issue, we use the first character of a *)
(* message's name.                              *)
(* <parsers and [[xdef]] streams for \usmalltalk>= *)
fun arity name =
      let val cs = explode name
      in  if Char.isAlpha (hd cs) then
            length (List.filter (fn c => c = #":") cs)
          else
            1
      end

fun arityOk name args = arity name = length args

fun arityErrorAt loc what msgname args =
  let fun argn n = if n = 1 then "1 argument" else intString n ^ " arguments"
  in  errorAt ("in " ^ what ^ ", message " ^ msgname ^ " expects " ^
                         argn (arity msgname) ^ ", but gets " ^
                         argn (length args)) loc
  end
(* <parsers and [[xdef]] streams for \usmalltalk>= *)
fun isImmutable x =
  List.exists (fn x' => x' = x) ["true", "false", "nil", "self", "super"] 
val immutable = sat isImmutable name

val mutable =
  let fun can'tMutate (loc, x) =
        ERROR (srclocString loc ^
               ": you cannot set or val-bind pseudovariable " ^ x)
  in  can'tMutate <$>! @@ immutable <|> OK <$>! name
  end
(* <parsers and [[xdef]] streams for \usmalltalk>= *)
val atomicExp =  LITERAL <$> NUM    <$> int
             <|> LITERAL <$> SYM    <$> (sym <|> (quote *> name)
                                             <|> (quote *> (intString <$> int)))
             <|> SUPER              <$  eqx "super" name
             <|> VAR                <$> name
(* <parsers and [[xdef]] streams for \usmalltalk>= *)
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
(* <boxed values 45>=                           *)
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
(* <boxed values 46>=                           *)
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
(* <boxed values 47>=                           *)
val _ = op kw : string -> string parser
val _ = op usageParsers : (string * 'a parser) list -> 'a parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

fun formalsIn context = formalsOf "(x1 x2 ...)" name context
fun sendClass (loc, e) = SEND (loc, e, "class", [])
fun exptable exp = usageParsers
  [ ("(set x e)",             curry SET       <$> mutable <*> exp)
  , ("(begin e ...)",               BEGIN     <$> many exp)
  , ("(primitive p e ...)",   curry PRIMITIVE <$> name <*> many exp)
  , ("(return e)",                  RETURN    <$> exp)
  , ("(block (x ...) e ...)", curry BLOCK     <$> formalsIn "block" <*> many exp
                                                                               )
  , ("(class e)",                   sendClass <$> @@ exp)
  , ("(locals x ...)",
     pure () <!> "found '(locals ...)' where an expression was expected")
  ]
(* <parsers and [[xdef]] streams for \usmalltalk>= *)
fun exp tokens = (
      atomicExp
  <|> quote       *> (VALUE <$> quotelit)
                                      (* not while reading predefined classes *)
  <|> curlyBracket ("{exp ...}", curry BLOCK [] <$> many exp)
  <|> exptable exp
  <|> liberalBracket ("(exp selector ...)",
                      messageSend <$> exp <*> @@ name <*>! many exp)
  <|> liberalBracket ("(exp selector ...)", noMsg <$>! @@ exp)
  <|> left *> right <!> "empty message send ()"
  ) 
  tokens
and noReceiver (loc, m) = errorAt ("sent message " ^ m ^ " to no object") loc
and noMsg (loc, e) = errorAt ("found receiver " ^ expString e ^
                                                         " with no message") loc
and messageSend receiver (loc, msgname) args = 
      if arityOk msgname args then
          OK (SEND (loc, receiver, msgname, args))
      else
          arityErrorAt loc "message send" msgname args
(* If any uSmalltalk code tries to change any of the *)
(* predefined ``pseudovariables,'' the [[settable]] *)
(* parser causes an error.                      *)

(* <parsers and [[xdef]] streams for \usmalltalk>= *)
and quotelit tokens = (
         mkSymbol  <$> name
    <|>  mkInteger <$> int
    <|>  shaped ROUND  left <&> mkArray <$> bracket("(literal ...)", many
                                                                       quotelit)
    <|>  shaped SQUARE left <&> mkArray <$> bracket("(literal ...)", many
                                                                       quotelit)
    <|>  quote               <!> "' within ' is not legal" 
    <|>  shaped CURLY  left  <!> "{ within ' is not legal"
    <|>  shaped CURLY  right <!> "} within ' is not legal"
    ) tokens
and shaped shape delim = sat (fn (_, s) => s = shape) delim
(* Here's the parser.                           *)
(* <boxed values 71>=                           *)
val _ = op name : string parser
val _ = op int  : int    parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* If parser [[exp]] sees something it doesn't  *)
(* recognize, it can't result in an error---because it *)
(* is used in \monoboxmany exp, it must simply fail. [*] *)
(* <boxed values 71>=                           *)
val _ = op exp      : exp parser
val _ = op quotelit : value parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* The remaining parser functions are mostly    *)
(* straightforward. The [[quotelit]] function may call *)
(* [[mkSymbol]], [[mkInteger]], or [[mkArray]], which *)
(* must not be called until after the initial basis is *)
(* read in. Function [[quotelit]] is recursive and is *)
(* called by [[exp]], so I define it as if it were *)
(* mutually recursive with [[exp]].             *)
(* <boxed values 71>=                           *)
val _ = op quotelit : value parser
(* <parsers and [[xdef]] streams for \usmalltalk>= *)
val printable = name <|> implode <$> intchars

val testtable = usageParsers
  [ ("(check-expect e1 e2)", curry CHECK_EXPECT <$> exp <*> exp)
  , ("(check-assert e)",           CHECK_ASSERT <$> exp)
  , ("(check-error e)",            CHECK_ERROR  <$> exp)
  , ("(check-print e chars)", curry CHECK_PRINT <$> exp <*> printable)
  ]
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
(* <boxed values 72>=                           *)
val _ = op testtable : unit_test parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <parsers and [[xdef]] streams for \usmalltalk>= *)
val method =
  let val locals = usageParsers [("[locals y ...]", many name)] <|> pure []
      fun imp kind = curry3 id <$> @@ (formalsIn kind) <*> locals <*> many exp
      fun method kind name impl =
            check (kname kind, name, impl) >>=+
            (fn (formals, locals, body) =>
                { flavor = kind, name = name, formals = formals, locals = locals
                , body = body })
      and kname IMETHOD = "method"
        | kname CMETHOD = "class-method"
      and check (kind, name, (formals as (loc, xs), locals, body)) = 
            if arityOk name xs then
              OK (xs, locals, BEGIN body)
            else
              arityErrorAt loc (kind ^ " definition") name xs
  in  usageParsers
      [ ("(method f (args) body)", method IMETHOD <$> name <*>! imp "method")
      , ("(class-method f (args) body)",
                                   method CMETHOD <$> name <*>! imp
                                                                 "class method")
      ]
  end
(* The parser for definitions recognizes [[method]] and *)
(* [[class-method]], because if a class definition has *)
(* an extra right parenthesis, a [[method]] or  *)
(* [[class-method]] keyword might show up at top level. *)
(* <boxed values 73>=                           *)
val _ = op method : method_def parser
val parseMethods = many method <* many eol <* eos
(* <parsers and [[xdef]] streams for \usmalltalk>= *)
fun classDef name super ivars methods =
      CLASSD { name = name, super = super, ivars = ivars, methods = methods }

val ivars = nodups ("instance variable", "class definition") <$>! @@ (many name)

val subclass_of = usageParsers [("[subclass-of className]", name)]
val ivars = (fn xs => getOpt (xs, [])) <$> 
            optional (usageParsers [("[ivars name...]", ivars)])

val deftable = usageParsers
  [ ("(val x e)", curry  VAL    <$> mutable <*> exp)
  , ("(define f (args) body)",
                  curry3 DEFINE <$> name <*> formalsIn "define" <*> exp)
  , ("(class name [subclass-of ...] [ivars ...] methods)",
                  classDef <$> name <*> subclass_of <*> ivars <*> many method
              <|> (EXP o sendClass) <$> @@ exp)

  ]
(* True definitions.                            *)
(* <boxed values 74>=                           *)
val _ = op deftable : def parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <parsers and [[xdef]] streams for \usmalltalk>= *)
val xdeftable = 
  let fun bad what =
        "unexpected `(" ^ what ^ "...'; " ^
        "did a class definition end prematurely?"
  in  usageParsers
      [ ("(use filename)",      USE <$> name)
      , ("(method ...)",        pzero <!> bad "method")
      , ("(class-method ...)",  pzero <!> bad "class-method")
      ]
  end

val xdef =  DEF  <$> deftable
        <|> TEST <$> testtable
        <|> xdeftable
        <|> badRight "unexpected right bracket"
        <|> DEF <$> EXP <$> exp
        <?> "definition"
(* Extended definitions.                        *)
(* <boxed values 75>=                           *)
val _ = op xdeftable : xdef parser
val _ = op xdef      : xdef parser
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <parsers and [[xdef]] streams for \usmalltalk>= *)
val xdefstream = interactiveParsedStream (smalltalkToken, xdef)
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
(* <boxed values 110>=                          *)
val _ = op xdefstream   : string * line stream     * prompts -> xdef stream
val _ = op filexdefs    : string * TextIO.instream * prompts -> xdef stream
val _ = op stringsxdefs : string * string list               -> xdef stream



(*****************************************************************)
(*                                                               *)
(*   EVALUATION, TESTING, AND THE READ-EVAL-PRINT LOOP FOR \USMALLTALK *)
(*                                                               *)
(*****************************************************************)

(* Extended definitions are evaluated by the shared *)
(* read-eval-print loop. And because of the way *)
(* primitives are used in the evaluator, it needs more *)
(* supporting code than in other bridge languages. *)
(* <evaluation, testing, and the read-eval-print loop for \usmalltalk>= *)
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

(* The interpreter has one more circularity to manage. *)
(* Before we can define values of the built-in classes, *)
(* we have to define the classes themselves. And before *)
(* we can define the built-in classes, we have to define *)
(* the primitives that are used in those classes. But *)
(* there are primitives that depend on [[nil]], which is *)
(* a value of a built-in class! For example, when we *)
(* create a new array, its contents are initially  *)
(* [[nil]]. To arrange for the right definitions to *)
(* appear in the right order, I organize code for *)
(* primitives and built-in classes in two layers. *)
(*                                              *)
(* The first layer includes chunks [[<<ML functions for *)
(* [[Object]]'s and [[UndefinedObject]]'s primitives>>]] *)
(* and [[<<built-in classes [[Object]] and      *)
(* [[UndefinedObject]]>>]]. This code defines   *)
(* [[Object]], which enables us to define       *)
(* [[UndefinedObject]], which enables us to define *)
(* [[nilValue]] (the internal representation of  *)
(* [[nil]]). The second layer includes chunks [[<<ML *)
(* functions for remaining classes' primitives>>]] and *)
(* [[]]. They define all                        *)
(* the other primitives and built-in classes, some of *)
(* which use [[nilValue]].                      *)
(* <support for primitives and built-in classes>= *)
(* <utility functions for building primitives in \usmalltalk>= *)
type primitive = value list * value ref env -> value
fun arityError n args =
  raise RuntimeError ("primitive expected " ^ intString n ^
                      " arguments; got " ^ intString (length args))
fun unaryPrim  f = (fn ([a],    _) => f  a     | (vs, _) => arityError 0 vs) :
                                                                       primitive
fun binaryPrim f = (fn ([a, b], _) => f (a, b) | (vs, _) => arityError 1 vs) :
                                                                       primitive
(* Utilities for creating primitives            *)
(*                                              *)
(* Most primitives are created directly from    *)
(* ML functions. As in the interpreter for micro-Scheme *)
(* (\crefmlscheme.chap), I build what I need in stages. *)
(* Here I first turn unary and binary functions into *)
(* primitives, then turn primitives into methods. *)
(* <boxed values 64>=                           *)
val _ = op unaryPrim  : (value         -> value) -> primitive
val _ = op binaryPrim : (value * value -> value) -> primitive
(* <utility functions for building primitives in \usmalltalk>= *)
fun internalParse parser ss =
  let val synopsis = case ss of [s] => s
                              | ["(begin ", s, ")"] => s
                              | s :: ss => s ^ "..." 
                              | [] => ""
      val name = "internal syntax"
      val input = interactiveParsedStream (smalltalkToken, parser)
                                          (name, streamOfList ss, noPrompts)
      exception BadUserMethodInInterpreter of string (* can't be caught *)
  in  case streamGet input
        of SOME (e, _) => e
         | NONE => (app eprintln ("Failure to parse:" :: ss)
                   ; raise BadUserMethodInInterpreter (concat ss))
  end
(* A few primitives are more easily created as user *)
(* methods. To make it easy to create user methods *)
(* I define function [[userMethod]]. There is one dodgy *)
(* bit: the [[superclass]] field of the user method. *)
(* Because this class is used only to define the meaning *)
(* of messages to [[super]], and because none of my *)
(* predefined user methods sends messages to [[super]], *)
(* I can get away with a bogus superclass that  *)
(* understands no messages. The bogus superclass is not *)
(* the actual superclass of the class where the method *)
(* will be used, but no program can tell the difference. *)
(*                                              *)
(* Function [[internalExp]] is an auxiliary function *)
(* used to parse a string into abstract syntax; it calls *)
(* parser [[exp]] from \crefusma.code.exp.      *)
(* <boxed values 65>=                           *)
val _ = op internalParse : 'a parser -> string list -> 'a
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <metaclass utilities>=                       *)
fun metaclass (CLASS { class = ref meta, ... }) =
  case meta of META c => c
             | PENDING => raise InternalError "pending class"

fun classObject c = (metaclass c, CLASSREP c)
(* Function [[classObject]] uses [[CLASSREP]] to make *)
(* the class a [[rep]], then pairs it with the class of *)
(* which it is an instance, that is, its metaclass. *)
(* Any attempt to refer to an uninitialized metaclass *)
(* results in a checked run-time error.         *)
(* <boxed values 8>=                            *)
val _ = op metaclass   : class -> class
val _ = op classObject : class -> value
(* [*]                                          *)

(* <metaclass utilities>=                       *)
fun setMeta (CLASS { class = m as ref PENDING, ... }, meta) = m := META meta
  | setMeta (CLASS { class = ref (META _), ... }, _) =
      raise InternalError "double patch"
(* <\ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives>= *)
fun errorPrim msg = fn _ => raise RuntimeError msg
(* <\ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives>= *)
fun methodDefns (superMeta, super) ms =
  let fun method { flavor, name, formals, locals, body } =
            { name = name, formals = formals, body = body, locals = locals
            , superclass = case flavor of IMETHOD => super
                                        | CMETHOD => superMeta
            }
      fun addMethodDefn (m as { flavor = CMETHOD, ... }, (c's, i's)) = (method m
                                                                    :: c's, i's)
        | addMethodDefn (m as { flavor = IMETHOD, ... }, (c's, i's)) = (c's,
                                                                method m :: i's)
(* <boxed values 61>=                           *)
val _ = op methodDefns : class * class -> method_def list -> method list *
                                                                     method list
val _ = op method : method_def -> method
  in  foldr addMethodDefn ([], []) ms
  end
(* <\ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives>= *)
fun findClass (supername, xi) =
  case !(find (supername, xi))
    of (meta, CLASSREP c) => (meta, c)
     | v => raise RuntimeError ("object " ^ supername ^ " = " ^ valueString v ^
                                " is not a class")
(* The object named as a superclass must in fact *)
(* represent a class, so its representation must be *)
(* [[CLASSREP c]], where [[c]] is the class it  *)
(* represents. That object is an instance of its *)
(* metaclass. Function [[findClass]] returns the *)
(* metaclass and the class.                     *)
(* <boxed values 62>=                           *)
val _ = op findClass : name * value ref env -> class * class
(* <\ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives>= *)
fun eqRep ((cx, x), (cy, y)) = 
  classId cx = classId cy andalso
  case (x, y)
    of (ARRAY x,    ARRAY    y) => x = y
     | (NUM   x,    NUM      y) => x = y
     | (SYM   x,    SYM      y) => x = y
     | (USER  x,    USER     y) => x = y
     | (CLOSURE  x, CLOSURE  y) => false
     | (CLASSREP x, CLASSREP y) => classId x = classId y
     | _ => false
(* Two classes are the same object if and only if they *)
(* have the same unique identifier.             *)
(* <boxed values 67>=                           *)
val _ = op eqRep : value * value -> bool
(* Class membership                             *)
(*                                              *)
(* For [[memberOf]], the class [[c]] of [[self]] has to *)
(* be the same as the class [[c']] of the argument. For *)
(* [[kindOf]], it just has to be a subclass.    *)
(* <\ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives>= *)
fun memberOf ((c, _), (_, CLASSREP c')) = mkBoolean (classId c = classId c')
  | memberOf _ = raise RuntimeError "argument of isMemberOf: must be a class"

fun kindOf ((c, _), (_, CLASSREP (CLASS {class=u', ...}))) =
      let fun subclassOfClassU' (CLASS {super, class=u, ... }) =
            u = u' orelse (case super of NONE => false | SOME c =>
                                                            subclassOfClassU' c)
      in  mkBoolean (subclassOfClassU' c)
      end
  | kindOf _ = raise RuntimeError "argument of isKindOf: must be a class"
(* The [[error:]] primitive raises [[RuntimeError]]. *)
(* <\ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives>= *)
fun error (_, (_, SYM s)) = raise RuntimeError s
  | error (_, (c, _    )) =
      raise RuntimeError ("error: got class " ^ className c ^
                                                            "; expected Symbol")
(* Order of definition:                         *)
(*                                              *)
(* (object undef nilValue class metaclass       *)
(*  object-meta undef-meta class-meta meta-meta) *)
(*                                              *)
(* Utility functions for parsing internal method *)
(* definitions                                  *)
(*                                              *)
(* <utility functions for parsing internal method definitions>= *)
val bogusSuperclass = CLASS { name = "bogus superclass", super = NONE
                            , ivars = [], methods = ref [ ], class = ref PENDING
                            }
val internalMethodDefns = methodDefns (bogusSuperclass, bogusSuperclass)
fun internalMethods strings =
  case (internalMethodDefns o internalParse parseMethods) strings
    of ([], imethods) => imethods 
     | (_ :: _, _) => raise InternalError "primitive class has class methods"
(* Class [[Object]] is the ultimate superclass. *)
(* To support the implementation of [[self]], it has one *)
(* instance variable, [[self]]. Putting the instance *)
(* variable here ensures that every user-defined object *)
(* has an instance variable called [[self]], into which, *)
(* when a new object is created, function       *)
(* [[newUserObject]] places a pointer to the object *)
(* itself (\chunkrefsmall.chunk.newUserObject). \ *)
(* makenowebnotdef(from \chunkref               *)
(* small.chunk.object-methods)                  *)
(* <built-in class [[Object]]>=                 *)
val objectMethods = internalMethods 
                                     [
                              ";  Notions of equivalence                       "
                                     ,
                              ";                                               "
                                     ,
                            ";  To get equality right, Smalltalk uses the same "
                                     ,
                       ";  methodology as \\mcl. The methodology is based on a "
                                     ,
                         ";  central principle of programming-language theory, "
                                     ,
                       ";  called observational equivalence. The pointy-headed "
                                     ,
                           ";  theory idea is, speaking informally, that ``two "
                                     ,
                      ";  things are observationally equivalent if there is no "
                                     ,
                        ";  computational context that can distinguish them.'' "
                                     ,
                              ";  If we specialize this idea for equality and  "
                                     ,
                       ";  programming, we get something that makes more sense "
                                     ,
                           ";  to a programmer who doesn't normally talk about "
                                     ,
                              ";  computational contexts:                      "
                                     ,
                              ";                                               "
                                     ,
                              ";   Two values should be considered equal if no "
                                     ,
                              ";   program can tell them apart.                "
                                     ,
                              ";                                               "
                                     ,
                       ";  This principle is the guiding principle behind ML's "
                                     ,
                     ";  polymorphic equality. The principle has two immediate "
                                     ,
                              ";  consequences:                                "
                                     ,
                              ";                                               "
                                     ,
                    ";    • When you're comparing mutable abstractions, like "
                                     ,
                           ";   dictionaries, an object may compare equal only "
                                     ,
                              ";   with itself. That's because if you have two "
                                     ,
                             ";   different mutable objects, you can tell them "
                                     ,
                          ";   apart by mutating one and seeing that the other "
                                     ,
                              ";   doesn't change. Therefore, on mutable data, "
                                     ,
                         ";   equality must be implemented as object identity. "
                                     ,
                         ";    • When you're comparing immutable, non-atomic "
                                     ,
                        ";   representations like large integers, structurally "
                                     ,
                             ";   similar representations should be considered "
                                     ,
                              ";   equal.                                      "
                                     ,
                              ";                                               "
                                     ,
                       ";  In Smalltalk, object identity is implemented by the "
                                     ,
                     ";  [[==]] method. Here is how object identity is defined "
                                     ,
                              ";  on class [[Object]]: [*]                     "
                                     ,
                              ";  <methods of class [[Object]]>=               "
                                     ,
                  "(method ==  (anObject) (primitive sameObject self anObject))"
                                     ,
                              "(method !== (anObject) ((self == anObject) not))"
                                     ,
                        ";  The problem with observation by ``any program'' is "
                                     ,
                     ";  the same as the problem with object identity and with "
                                     ,
                        ";  ML's polymorphic identity: \\stdbreak sometimes it "
                                     ,
                     ";  says two things are different when they really should "
                                     ,
                     ";  be considered the same. When you're trying to tell if "
                                     ,
                       ";  objects are equivalent, there are some observations "
                                     ,
                              ";  you might want to rule out:                  "
                                     ,
                              ";                                               "
                                     ,
                     ";    • You might want to rule out mutation as a way of "
                                     ,
                        ";   observing differences. For example, perhaps right "
                                     ,
                              ";   now lists [[ns]] and [[ms]] have the same   "
                                     ,
                              ";   elements, so you'd like to consider them    "
                                     ,
                             ";   equivalent, even if adding number 80 to list "
                                     ,
                         ";   [[ns]] (but not [[ms]]) would enable you to tell "
                                     ,
                             ";   them apart. \\stdbreak                       "
                                     ,
                     ";    • When you're comparing abstractions, they should "
                                     ,
                           ";   be considered equivalent if no client code can "
                                     ,
                         ";   tell them apart. For example, if finite maps are "
                                     ,
                              ";   represented as association lists, and if no "
                                     ,
                          ";   combination of [[find]] and [[bind]] operations "
                                     ,
                             ";   can tell two maps apart, then they should be "
                                     ,
                              ";   considered equivalent, even if they are     "
                                     ,
                             ";   represented differently (\\cpageref          "
                                     ,
                             ";   scheme.alist-equality). \\stdbreak           "
                                     ,
                   ";    • Finally, in a language like Smalltalk, we want to "
                                     ,
                         ";   rule out reflection as a means of distinguishing "
                                     ,
                              ";   objects. For example, sending the [[class]] "
                                     ,
                         ";   message to try to distinguish two objects should "
                                     ,
                            ";   be considered the same kind of observation as "
                                     ,
                              ";   poking at the representation.               "
                                     ,
                              ";                                               "
                                     ,
                          ";  \\stdbreak To decide equivalence of two objects, "
                                     ,
                           ";  uSmalltalk rules out all of these observations: "
                                     ,
                              ";                                               "
                                     ,
                        ";   Two objects are considered equivalent if, without "
                                     ,
                          ";   mutating either object, client code cannot tell "
                                     ,
                              ";   them apart.                                 "
                                     ,
                              ";                                               "
                                     ,
                     ";  In Smalltalk, this is the equivalence that is used by "
                                     ,
                      ";  [[check-expect]], and it is implemented by the [[=]] "
                                     ,
                     ";   method. Each class has to think for itself about how "
                                     ,
                              ";  [[=]] should be defined, but as a default, a "
                                     ,
                     ";  conservative approximation is defined on all objects: "
                                     ,
                              ";  <methods of class [[Object]]>=               "
                                     ,
                                     "(method =  (anObject) (self == anObject))"
                                     ,
                                "(method != (anObject) ((self = anObject) not))"
                                     ,
                              ";  On [[Object]], they are                      "
                                     ,
                              ";  <methods of class [[Object]]>=               "
                                     , "(method isNil  () false)"
                                     , "(method notNil () true)"
                                     ,
                              ";  Implementations of some predefined classes   "
                                     ,
                              ";                                               "
                                     ,
                         ";  Classes whose implementations aren't shown in the "
                                     ,
                              ";  chapter.                                     "
                                     ,
                              ";                                               "
                                     ,
                              ";  Methods of primitive classes                 "
                                     ,
                              ";                                               "
                                     ,
                              ";  <methods of class [[Object]]>=               "
                                     ,
      "(method print () ('< print) (((self class) name) print) ('> print) self)"
                                     ,
                         "(method println () (self print) (newline print) self)"
                                     ,
                                "(method class ()       (primitive class self))"
                                     ,
               "(method isKindOf:    (aClass) (primitive isKindOf self aClass))"
                                     ,
             "(method isMemberOf:  (aClass) (primitive isMemberOf self aClass))"
                                     ,
                        "(method error:       (msg) (primitive error self msg))"
                                     ,
    "(method subclassResponsibility () (primitive subclassResponsibility self))"
                                     ,
                    "(method leftAsExercise () (primitive leftAsExercise self))"
                                      ]
val objectClass = 
  CLASS { name = "Object", super = NONE, ivars = ["self"], class = ref PENDING
        , methods = ref (methodsEnv objectMethods)
        }
val () = if logging then app print ["\nops.class { name = ", q "Object",
                ", methods = { ", commaSep (map (q o methodName) objectMethods),
                     " }, subclass_responsibilities = { } }\n"] else () (*OMIT*)
(* The [[]] are defined                         *)
(* throughout this chapter and in \crefusma.chap, *)
(* starting in \chunkrefsmall.chunk.object-methods. *)
(*                                              *)
(* Class [[UndefinedObject]], whose sole instance is  *)
(* [[nil]], redefines [[isNil]], [[notNil]], and *)
(* [[print]], as shown in chunks [->] and [->]. \ *)
(* makenowebnotdef(from \chunkref               *)
(* small.chunk.nil-methods)                     *)
(* <built-in class [[UndefinedObject]] and value [[nilValue]]>= *)
val nilClass = 
  mkClass "UndefinedObject" PENDING objectClass []
    (internalMethods 
                      [
                    ";  Here's how not to do it—two ways to test for [[nil]] "
                      ,
                     ";  by evaluating an expression: {smallverbatimx} (method "
                      ,
                      ";  isNil () (self == nil)) ; embarrassing (method isNil "
                      , ";  () (self isMemberOf: UndefinedObject)) ; more "
                      , ";  embarrassing {smallverbatimx} A real Smalltalk "
                      , ";  programmer sneers at this code. The proper way to "
                      , ";  implement case analysis is to use method dispatch. "
                      ,
                      ";  For [[isNil]] there are only two possible cases: the "
                      , ";  method should answer [[true]] or [[false]].  "
                      ,
                      ";  We arrange that on the [[nil]] object, the [[isNil]] "
                      ,
                       ";  method answers \\stdbreak [[true]], and that on all "
                      ,
                     ";  other objects, it answers [[false]]. We need only two "
                      ,
                     ";  method definitions: one on class [[UndefinedObject]], "
                      , ";  which is used only to answer messages sent to  "
                      ,
                    ";  [[nil]], \\stdbreak and one on class [[Object]], which "
                      , ";  all other classes inherit. We implement [[notNil]] "
                      , ";  the same way. The definitions on class       "
                      , ";  [[UndefinedObject]] are [*]                  "
                      , ";  <methods of class [[UndefinedObject]]>=      "
                      , "(method isNil  () true)"
                      , "(method notNil () false)"
                      , ";  [*]                                          "
                      , ";  <methods of class [[UndefinedObject]]>=      "
                      , "(method print () ('nil print) self)"
                       ])
(* The single instance of [[UndefinedObject]],  *)
(* internally called [[nilValue]], is created here, so *)
(* it can be returned from some primitives.     *)
(* <built-in class [[UndefinedObject]] and value [[nilValue]]>= *)
val nilValue = 
  let val nilCell  = ref (nilClass, USER []) : value ref
      val nilValue = (nilClass, USER (bind ("self", nilCell, emptyEnv)))
      val _        = nilCell := nilValue
  in  nilValue
  end
(* Unlike Scheme, Smalltalk does not have a syntactic *)
(* form that evaluates code inside a closure. Instead, *)
(* Smalltalk uses the [[value]] primitive. The [[value]] *)
(* primitive is the only primitive that is mutually *)
(* recursive with [[eval]]; it uses the function stored *)
(* in [[applyClosureRef]]. [*]                  *)
(* <\ml\ functions for remaining classes' primitives>= *)
type closure = name list * exp list * value ref env * class * frame
val applyClosureRef : (closure * value list * value ref env -> value) ref
  = ref (fn _ => raise InternalError "applyClosureRef not set")

fun valuePrim ((_, CLOSURE clo) :: vs, xi) = !applyClosureRef (clo, vs, xi)
  | valuePrim _ = raise RuntimeError "primitive `value` needs a closure"
(* The [[class]] primitive takes an object as its single *)
(* argument. The object is represented by a pair that *)
(* includes the object's class, which is promoted to a *)
(* full object by calling function [[classObject]] (\ *)
(* chunkrefsmall.chunk.classObject).            *)
(* <\ml\ functions for remaining classes' primitives>= *)
val classPrimitive = unaryPrim (fn (c, rep) => classObject c)
(* <\ml\ functions for remaining classes' primitives>= *)
local
  fun mkIvars (CLASS { ivars, super, ... }) =
    let val supervars = case super of NONE => emptyEnv | SOME c => mkIvars c
    in  foldl (fn (x, rho) => bind (x, ref nilValue, rho)) supervars ivars
    end
in
  fun newUserObject c =
        let val ivars = mkIvars c
            val self = (c, USER ivars)
        in  (find ("self", ivars) := self; self)
        end
(* The [[newUserObject]] primitive allocates fresh *)
(* instance variables, each containing [[nilValue]]. *)
(* It then allocates the object, and finally it assigns *)
(* [[self]] to point to the object itself. [*]  *)
(* <boxed values 15>=                           *)
val _ = op mkIvars       : class -> value ref env
val _ = op newUserObject : class -> value
end
(* <\ml\ functions for remaining classes' primitives>= *)
fun classPrim f = 
  unaryPrim (fn (meta, CLASSREP c) => f (meta, c)
              | _ => raise RuntimeError "class primitive sent to non-class")
(* The class primitives take both the metaclass and the *)
(* class as arguments.                          *)
(* <boxed values 66>=                           *)
val _ = op classPrim : (class * class -> value) -> primitive
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* <\ml\ functions for remaining classes' primitives>= *)
fun superclassObject (_, CLASS { super = NONE, ... })   = nilValue
  | superclassObject (_, CLASS { super = SOME c, ... }) = classObject c
(* Arithmetic with overflow                     *)
(*                                              *)
(* The implementations of the primitives are easy; we *)
(* try to build a block containing the result, but if *)
(* the computation overflows, we answer the overflow *)
(* block instead.                               *)
(* <\ml\ functions for remaining classes' primitives>= *)
fun withOverflow binop ([(_, NUM n), (_, NUM m), ovflw], xi) =
      (mkBlock ([], [VALUE (mkInteger (binop (n, m)))], emptyEnv, objectClass,
                                                                        noFrame)
       handle Overflow => ovflw)
  | withOverflow _ ([_, _, _], _) =
      raise RuntimeError "numeric primitive with overflow expects numbers"
  | withOverflow _ _ =
      raise RuntimeError "numeric primitive with overflow expects 3 arguments"
(* Integer primitives                           *)
(*                                              *)
(* Integers print using the [[intString]] function *)
(* defined in \crefmlinterps.chap. [*]          *)
(* <\ml\ functions for remaining classes' primitives>= *)
fun printInt (self as (_, NUM n)) = ( xprint (intString n); self )
  | printInt _ = raise RuntimeError (
                                   "cannot print when object inherits from Int")
(* The also support UTF-8 printing.             *)

(* <\ml\ functions for remaining classes' primitives>= *)
fun printu (self as (_, NUM n)) = ( printUTF8 n; self )
  | printu _ = raise RuntimeError ("receiver of printu is not a small integer")
(* <\ml\ functions for remaining classes' primitives>= *)
fun binaryInt mk operator ((_, NUM n), (_, NUM m)) = mk (operator (n, m))
  | binaryInt _ _         ((_, NUM n), (c, _)) =
      raise RuntimeError ("numeric primitive expected numeric argument, got <"
                          ^ className c ^ ">")
  | binaryInt _ _         ((c, _), _) =
      raise RuntimeError ("numeric primitive method defined on <" ^ className c
                                                                          ^ ">")
fun arithop    operator = binaryPrim (binaryInt mkInteger operator)
fun intcompare operator = binaryPrim (binaryInt mkBoolean operator)
(* A binary integer operation created with [[arith]] *)
(* expects as arguments two integers [[m]] and [[n]]; it *)
(* applies an [[operator]] to them and uses a creator *)
(* function [[mk]] to convert the result to a value. *)
(* I use [[binaryInt]] to build arithmetic and  *)
(* comparison.                                  *)
(* <boxed values 68>=                           *)
val _ = op binaryInt  : ('a -> value) -> (int * int -> 'a)   -> value * value ->
                                                                           value
val _ = op arithop    :                  (int * int -> int)  -> primitive
val _ = op intcompare :                  (int * int -> bool) -> primitive
(* To create a new integer, you must pass the integer *)
(* class, plus an argument that is represented by an *)
(* integer.                                     *)
(* <\ml\ functions for remaining classes' primitives>= *)
fun newInteger ((_, CLASSREP c), (_, NUM n)) = (c, NUM n)
  | newInteger _ = raise RuntimeError (
                                   "made new integer with non-int or non-class")
(* Symbol primitives                            *)
(*                                              *)
(* A symbol prints as its name, with no leading [[']]. *)
(* <\ml\ functions for remaining classes' primitives>= *)
fun printSymbol (self as (_, SYM s)) = (xprint s; self)
  | printSymbol _ = raise RuntimeError
                                 "cannot print when object inherits from Symbol"
(* To create a new symbol, you must pass an argument *)
(* that is represented by a symbol.             *)
(* <\ml\ functions for remaining classes' primitives>= *)
fun newSymbol ((_, CLASSREP c), (_, SYM s)) = (c, SYM s)
  | newSymbol _ = raise RuntimeError (
                                 "made new symbol with non-symbol or non-class")
(* A new array contains all [[nil]]. [*] [*]    *)
(* <\ml\ functions for remaining classes' primitives>= *)
fun newArray ((_, CLASSREP c), (_, NUM n)) = (c, ARRAY (Array.array (n, nilValue
                                                                             )))
  | newArray _ = raise RuntimeError
                                "Array new sent to non-class or got non-integer"
(* <\ml\ functions for remaining classes' primitives>= *)
fun arrayPrimitive f ((c, ARRAY a) :: vs, _) = f (a, vs)
  | arrayPrimitive f _ = raise RuntimeError "Array primitive used on non-array"

fun arraySize (a, []) = mkInteger (Array.length a)
  | arraySize (a, vs) = arityError 0 vs
(* To create primitives that expect [[self]] to be an *)
(* array, we define [[arrayPrimitive]].         *)
(* <boxed values 69>=                           *)
val _ = op arrayPrimitive : (value array * value list -> value) -> primitive
(* The array primitives for [[at:]] and [[at:put:]] use *)
(* Standard ML's [[Array]] module.              *)
(* <\ml\ functions for remaining classes' primitives>= *)
fun arrayAt (a, [(_, NUM n)]) = Array.sub (a, n)
  | arrayAt (_, [_])  = raise RuntimeError "Non-integer used as array subscript"
  | arrayAt (_, vs)   = arityError 1 vs

fun arrayUpdate (a, [(_, NUM n), x]) = (Array.update (a, n, x); nilValue)
  | arrayUpdate (_, [_, _]) = raise RuntimeError
                                           "Non-integer used as array subscript"
  | arrayUpdate (_, vs)     = arityError 2 vs
(* Block primitives                             *)
(*                                              *)
(* Class primitives                             *)
(*                                              *)
(* Showing protocols                            *)
(*                                              *)
(* The [[showProtocol]] function helps implement the *)
(* [[protocol]] and [[localProtocol]] primitives, which *)
(* are defined on class [[Class]]. Its implementation is *)
(* not very interesting. Function [[insert]] helps *)
(* implement an insertion sort, which we use to present *)
(* methods in alphabetical order.               *)
(* <\ml\ functions for remaining classes' primitives>= *)
local
  fun showProtocol doSuper kind c =
    let fun member x l = List.exists (fn x' : string => x' = x) l
        fun insert (x, []) = [x]
          | insert (x, (h::t)) =
              case compare x h
                of LESS    => x :: h :: t
                 | EQUAL   => x :: t (* replace *)
                 | GREATER => h :: insert (x, t)
        and compare (name, _) (name', _) = String.compare (name, name')
        fun methods (CLASS { super, methods = ref ms, name, ... }) =
              if not doSuper orelse (kind = "class-method" andalso name =
                                                                   "Class") then
                foldl insert [] ms
              else
                foldl insert (case super of NONE => [] | SOME c => methods c) ms
        fun show (name, { formals, ... } : method) =
              app xprint ["(", kind, " ", name,
                          " (", spaceSep formals, ") ...)\n"]
    in  app show (methods c)
    end
in
  fun protocols all (meta, c) =
    ( showProtocol all "class-method" meta
    ; showProtocol all "method" c
    ; (meta, CLASSREP c)
    )
end
(* <\ml\ functions for remaining classes' primitives>= *)
fun methodNames (_, CLASS { methods, ... }) = mkArray (map (mkSymbol o fst) (!
                                                                       methods))
(* <\ml\ functions for remaining classes' primitives>= *)
fun getMethod ((_, CLASSREP (c as CLASS { methods, name, ... })), (_, SYM s)) =
      (mkCompiledMethod (find (s, !methods))
       handle NotFound _ =>
         raise RuntimeError ("class " ^ className c ^ " has no method " ^ s))
      before (if logging then logGetMethod name s else ())
  | getMethod ((_, CLASSREP _), _) =
      raise RuntimeError "getMethod primitive given non-name"    
  | getMethod _ =
      raise RuntimeError "getMethod primitive given non-class"    
(* <\ml\ functions for remaining classes' primitives>= *)
fun removeMethod ((_, CLASSREP (c as CLASS { methods, ... })), (_, SYM s)) =
      (methods := List.filter (fn (m, _) => m <> s) (!methods); nilValue)
  | removeMethod ((_, CLASSREP _), _) =
      raise RuntimeError "removeMethod primitive given non-name"    
  | removeMethod _ =
      raise RuntimeError "removeMethod primitive given non-class"    
(* <\ml\ functions for remaining classes' primitives>= *)
fun setMethod [(_, CLASSREP c), (_, SYM s), (_, METHOD m)] =
      let val CLASS { methods, super, name = cname, ... } = c
          val superclass = case super of SOME s => s | NONE => c (* bogus *)
          val { name = _, formals = xs, locals = ys, body = e, superclass = _ }
                                                                             = m
          val m' = { name = s, formals = xs, locals = ys, body = e
                   , superclass = superclass }
          val _ = if arity s = length xs then ()
                  else raise RuntimeError ("compiled method with " ^
                                           countString xs "argument" ^
                                           " cannot have name `" ^ s ^ "`")
          val _ = if logging then logSetMethod cname s else ()
      in  (methods := bind (s, m', !methods); nilValue)
      end
  | setMethod [(_, CLASSREP _), (_, SYM s), m] =
      raise RuntimeError ("setMethod primitive given non-method " ^ valueString
                                                                              m)
  | setMethod [(_, CLASSREP _), s, _] =
      raise RuntimeError ("setMethod primitive given non-symbol " ^ valueString
                                                                              s)
  | setMethod [c, _, _] =
      raise RuntimeError ("setMethod primitive given non-class " ^ valueString c
                                                                               )
  | setMethod _ =
      raise RuntimeError "setMethod primitive given wrong number of arguments"
(* \savenowebnotdef Class [[Class]] is in the   *)
(* interpreter so that metaclasses can inherit from it, *)
(* and [[Metaclass]] is here so that each metaclass can *)
(* be an instance of it. \makenowebnotdef(from \chunkref *)
(* small.chunk.class-methods)                   *)
(* <built-in classes [[Class]] and [[Metaclass]]>= *)
val classClass =
  mkClass "Class" PENDING objectClass []
    (internalMethods 
                      [
                      ";  Most of the methods of class [[Class]] are relegated "
                      , ";  to \\crefusma.chap, but here I show the default "
                      , ";  implementation of [[new]]. [*]               "
                      , ";  <methods of class [[Class]]>=                "
                      , "(method new () (primitive newUserObject self))"
                      , ";  <methods of class [[Class]]>=                "
                      , "(method superclass () (primitive superclass self))"
                      , "(method name () (primitive className self))"
                      , "(method printProtocol () (primitive protocol self))"
                      ,
                 "(method printLocalProtocol () (primitive localProtocol self))"
                      ,
       "(method compiledMethodAt: (aSymbol) (primitive getMethod self aSymbol))"
                      ,
"(method addSelector:withMethod: (aSymbol aMethod) (primitive setMethod self aSymbol aMethod))"
                      , "(method addMethods:from: (names aClass)"
                      ,
"  (names do: [block (m) (self addSelector:withMethod: m (aClass compiledMethodAt: m))]))"
                      , "(method methodNames () (primitive methodNames self))"
                      , "(method addAllMethodsFrom: (aClass)"
                      , "  (self addMethods:from: (aClass methodNames) aClass))"
                      ,
      "(method removeSelector: (aSymbol) (primitive removeMethod self aSymbol))"
                       ])

val metaclassClass =
  mkClass "Metaclass" PENDING classClass []
    (internalMethods 
                      [ ";  For metaclasses, this default is overridden; "
                      , ";  a metaclass may not be used to instantiate new "
                      , ";  objects. [*]                                 "
                      , ";  <methods of class [[Metaclass]]>=  "
                      ,
         "(method new () (self error: 'a-metaclass-may-have-only-one-instance))"
                       ])
(* <metaclasses for built-in classes>=          *)
fun metaSuper (CLASS { super = NONE,   ... }) = classClass
  | metaSuper (CLASS { super = SOME c, ... }) = metaclass c
(* As noted above, a new metaclass inherits from the *)
(* metaclass of its superclass, unless there is no *)
(* superclass, in which case it inherits from [[Class]]. *)
(* Internal representation [[classClass]] is defined *)
(* below.                                       *)
(* <boxed values 9>=                            *)
val _ = op metaSuper : class -> class
(* <metaclasses for built-in classes>=          *)
fun mkMeta c methods =
  mkClass ("class " ^ className c) (META metaclassClass) (metaSuper c) []
                                                                         methods
(* To make a metaclass, we need to know the class [[c]] *)
(* of which the result is the metaclass, and the class *)
(* [[methods]]. The metaclass has a name derived from *)
(* [[c]]'s name and is an instance of class     *)
(* [[Metaclass]]. It has the superclass computed by *)
(* [[metaSuper]], no instance variables, and the given *)
(* [[methods]]. [*]                             *)
(* <boxed values 10>=                           *)
val _ = op mkMeta : class -> method list -> class
(* [[funty]] stand for \tau, [[actualtypes]]    *)
(* stand for \ldotsntau, and [[rettype]] stand for alpha *)
(* . The first premise is implemented by a call to *)
(* [[typesof]] and the second by a call to      *)
(* [[freshtyvar]]. The constraint is represented just as *)
(* written in the rule.                         *)

(* \restorenowebnotdef Internal classes [[classClass]] *)
(* and [[metaclassClass]] are used in the implementation *)
(* of [[mkMeta]], shown above in \chunkref      *)
(* small.chunk.mkMeta. Once [[mkMeta]] is defined, *)
(* it can be used to create the metaclasses of classes *)
(* [[Object]], [[UndefinedObject]], [[Class]], and *)
(* [[Metaclass]].                               *)
(* <metaclasses for built-in classes>=          *)
fun patchMeta c = setMeta (c, mkMeta c [])
val () = app patchMeta [objectClass, nilClass, classClass, metaclassClass]
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(* Most classes and metaclasses are created by calling *)
(* [[newClassObject]], which is given a class definition *)
(* and creates a class object and a metaclass object for *)
(* that class. The superclass and its metaclass are *)
(* found by looking up the named superclass in  *)
(* environment xi. Function [[methodDefns]] segregates *)
(* the method definitions into class methods and *)
(* instance methods, and it attaches the correct static *)
(* superclass to each method. The class is built using *)
(* [[mkClass]], and its metaclass is built using *)
(* [[mkMeta]]. [*]                              *)
(* <definition of [[newClassObject]] and supporting functions>= *)
fun newClassObject {name, super, ivars, methods} xi =
  let val (superMeta, super) = findClass (super, xi)
        handle NotFound s => raise RuntimeError ("Superclass " ^ s ^
                                                                   " not found")
      val (cmethods, imethods) = methodDefns (superMeta, super) methods
      val class = mkClass name PENDING super ivars imethods
      val ()    = setMeta (class, mkMeta class cmethods)
  in  classObject class
  end
(* Support for tracing                          *)
(*                                              *)
(* Tracing support is divided into three parts: support *)
(* for printing indented messages, which is conditioned *)
(* on the value of the variable [[ --- trace]]; support *)
(* for maintaining a stack of source-code locations, *)
(* which is used to provide information when an error *)
(* occurs; and exposed tracing functions, which are used *)
(* in the main part of the interpreter. To keep the *)
(* details hidden from the rest of the interpreter, the *)
(* first two parts are made [[local]].          *)
(* <functions for managing and printing a \usmalltalk\ stack trace>= *)
local
  (* <private state and functions for printing indented traces ((usm))>= *)
  fun traceMe xi =
    let val count = find("&trace", xi)
    in  case !count
          of (c, NUM n) =>
              if n = 0 then false
              else ( count := (c, NUM (n - 1))
                   ; if n = 1 then (xprint "<trace ends>\n"; false) else true
                   )
           | _ => false
    end handle NotFound _ => false
  (* The [[traceMe]] function is used internally to decide *)
  (* whether to trace; it not only returns a Boolean but *)
  (* also decrements [[ --- trace]] if needed.    *)
  (* <boxed values 76>=                           *)
  val _ = op traceMe : value ref env -> bool
  (* The local variable [[tindent]] maintains the current *)
  (* trace state; [[indent]] uses it to print an  *)
  (* indentation string.                          *)
  (* <private state and functions for printing indented traces ((usm))>= *)
  val tindent = ref 0
  fun indent 0 = ()
    | indent n = (xprint "  "; indent (n-1))
  (* Any actual printing is done by [[tracePrint]], *)
  (* conditional on [[traceMe]] returning [[true]]. The *)
  (* argument [[direction]] of type [[indentation]] *)
  (* controls the adjustment of [[indent]]. For   *)
  (* consistency, we outdent from the previous level *)
  (* before printing a message; we indent from the current *)
  (* level after printing a message.              *)
  (* <private state and functions for printing indented traces ((usm))>= *)
  datatype indentation = INDENT_AFTER | OUTDENT_BEFORE

  fun tracePrint direction xi f =
      if traceMe xi then
        let val msg = f () (* could change tindent *)
        in  ( if direction = OUTDENT_BEFORE then tindent := !tindent - 1 else ()
            ; indent (!tindent)
            ; app xprint msg
            ; xprint "\n"
            ; if direction = INDENT_AFTER   then tindent := !tindent + 1 else ()
            )
        end
      else
          ()    
  (* Printing of trace messages is conditional, but we *)
  (* always maintain a stack of source-code locations. The *)
  (* stack is displayed when an error occurs.     *)

(* <private state and functions for maintaining a stack of source-code locations ((usm))>= *)
  val locationStack = ref [] : (string * srcloc) list ref
  fun push srcloc = locationStack := srcloc :: !locationStack
  fun pop () = case !locationStack
                 of []     => raise InternalError "tracing stack underflows"
                  | h :: t => locationStack := t
in
  (* <exposed tracing functions ((usm))>=         *)
  fun resetTrace ()       = (locationStack := []; tindent := 0)
  fun traceIndent what xi = (push what; tracePrint INDENT_AFTER   xi)
  fun outdentTrace     xi = (pop ();    tracePrint OUTDENT_BEFORE xi)

  fun removeRepeat 0 xs = (0, [], xs)
    | removeRepeat n xs =
        let val header = List.take (xs, n) 
            fun count k xs =
              if (header = List.take (xs, n)) handle Subscript => false then
                count (k + 1) (List.drop (xs, n))
              else
                (k, header, xs)
        in  count 0 xs
        end handle Subscript => (0, [], xs)

  fun findRepeat xs k =
    if k > 20 then
      (0, [], xs)
    else
      let val repeat as (n, _, _) = removeRepeat k xs
      in  if n >= 3 then
            repeat
          else
            findRepeat xs (k + 1)
      end

  fun findRepeatAfter xs 3 = ([], (0, [], xs))
    | findRepeatAfter xs k =
        let val (n, header, ys) = findRepeat (List.drop (xs, k)) 1
        in  if n > 0 then
              (List.take(xs, k), (n, header, ys))
            else
              findRepeatAfter xs (k + 1)
        end handle Subscript => ([], (0, [], xs))

  fun showStackTrace condense =
    if null (!locationStack) then
      ()
    else
      let fun show (msg, (file, n)) =
            app xprint ["  Sent '", msg, "' in ", file, ", line ", intString n,
                                                                           "\n"]
          val preRepeat =
            if condense then findRepeatAfter (!locationStack) 0
            else ([], (0, [], !locationStack))
          val _ = xprint "Method-stack traceback:\n"
      in  case preRepeat
            of ([], (0, _, locs)) => app show locs 
             | (_,  (0, _, _)) => let exception Invariant in raise Invariant end
             | (prefix, (k, header, locs)) =>
                  ( app show prefix
                  ; if null prefix then ()
                    else app xprint [ "    ... loop of size "
                                    , Int.toString (length header) ,
                                                                 " begins ...\n"
                                    ]
                  ; app show header
                  ; app xprint [ "    ... loop of size ", Int.toString (length
                                                                         header)
                               , " repeated ", Int.toString k, " times ...\n"
                               ]
                  ; app show locs
                  )
      end
  fun eprintlnTrace s = ( eprintln s
                        ; showStackTrace (String.isSubstring
                                                         "recursion too deep" s)
                        ; resetTrace ()
                        )
  (* Here are the tracing-related functions that are *)
  (* exposed to the rest of the interpreter. The  *)
  (* interpreter uses [[traceIndent]] to trace sends, *)
  (* [[outdentTrace]] to trace answers, and [[resetTrace]] *)
  (* to reset indentation. And it uses [[eprintlnTrace]] *)
  (* to print an error message, show the stack trace, and *)
  (* reset the trace.                             *)
  (* <boxed values 77>=                           *)
  val _ = op resetTrace     : unit -> unit
  val _ = op traceIndent    : string * srcloc -> value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op outdentTrace   :                    value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op showStackTrace : bool -> unit
  val _ = op eprintlnTrace  : string -> unit
end
(* Primitives                                   *)
(*                                              *)
(* To find a primitive by name, I look it up in the *)
(* association list [[primitives]].             *)
(* <definition of [[primitives]]>=              *)
val primitives = (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("sameObject", binaryPrim (mkBoolean o eqRep)) ::
                 ("class",      classPrimitive) ::
                 ("isKindOf",   binaryPrim kindOf) ::
                 ("isMemberOf", binaryPrim memberOf) ::
                 ("error",      binaryPrim error) ::
                 ("subclassResponsibility",
                                errorPrim
              "subclass failed to implement a method it was responsible for") ::
                 ("leftAsExercise", errorPrim
                         "method was meant to be implemented as an exercise") ::
                 (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("newUserObject", classPrim (fn (meta, c) => newUserObject c))
                                                                              ::
                 ("superclass", classPrim superclassObject) ::
                 ("className", classPrim (fn (_, c) => mkSymbol (className c)))
                                                                              ::
                 ("protocol", classPrim (protocols true)) ::
                 ("localProtocol", classPrim (protocols false)) ::
                 ("getMethod", binaryPrim getMethod) ::
                 ("setMethod", setMethod o fst) ::
                 ("removeMethod", binaryPrim removeMethod) ::
                 ("methodNames", classPrim methodNames) ::
                 (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("value", valuePrim) ::
                 (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("addWithOverflow", withOverflow op + ) ::
                 ("subWithOverflow", withOverflow op - ) ::
                 ("mulWithOverflow", withOverflow op * ) ::
                 (* Hashing                                      *)
                 (*                                              *)
                 (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("hash", unaryPrim (fn (_, SYM s) => mkInteger (fnvHash s)
                                      | v => raise RuntimeError
                                          "hash primitive expects a symbol")) ::
                 (* Here are the primitive operations on small integers.  *)
                 (* [*]                                          *)
                 (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("newSmallInteger",   binaryPrim newInteger) ::
                 ("+",   arithop op +  )  ::
                 ("-",   arithop op -  )  ::
                 ("*",   arithop op *  )  ::
                 ("div", arithop op div)  ::
                 ("<",   intcompare op <) ::
                 (">",   intcompare op >) ::
                 ("printSmallInteger", unaryPrim printInt) ::     
                 ("printu",            unaryPrim printu)   ::     
                 (* In chunk [->], these primitives are used to define *)
                 (* class [[SmallInteger]].                      *)

                 (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("printSymbol", unaryPrim  printSymbol) ::
                 ("newSymbol",   binaryPrim newSymbol  ) ::
                 (* Here are all the primitive array methods. [*] *)
                 (* <primitives for \usmalltalk\ [[::]]>=        *)
                 ("arrayNew",    binaryPrim     newArray)   ::
                 ("arraySize",   arrayPrimitive arraySize)  ::
                 ("arrayAt",     arrayPrimitive arrayAt)    ::
                 ("arrayUpdate", arrayPrimitive arrayUpdate) ::
                 (* In chunk [->], these primitive methods are used to *)
                 (* define class [[Array]].                      *)
 nil
val () =   if isSome (OS.Process.getEnv "USMPRIM") then      (*OMIT*)
           app (println o fst) primitives else ()   (*OMIT*)
(* <helper functions for evaluation>=           *)
fun findMethod (name, class) =
  let fun fm (subclass as CLASS { methods, super, ...}) =
        find (name, !methods)
        before (if logging then logFind name subclass else ()) (*OMIT*)
        handle NotFound m =>
          case super
            of SOME c => fm c
             | NONE   => raise RuntimeError
                           (className class ^ " does not understand message " ^
                                                                              m)
(* All that remains is method search. If \      *)
(* sendToDispatchesm c imp, then calling \monofindMethod *)
(* (m, c) returns imp. If there is no imp such that \ *)
(* sendToDispatchesm c imp, then the same call raises *)
(* the [[RuntimeError]] exception.              *)
(* <boxed values 4>=                            *)
val _ = op findMethod : name * class -> method
val _ = op fm         : class        -> method
(* [*]                                          *)

  in  fm class
  end
(* Utilities                                    *)
(*                                              *)
(* Function [[optimizedBind]] is an optimized version *)
(* of [[bind]], just like the one used in \cref *)
(* impcore.chap. If a previous binding exists, it *)
(* overwrites the previous binding and does not change *)
(* the environment. The optimization is safe only *)
(* because no operation in uSmalltalk makes a copy of *)
(* the global environment.                      *)
(* <helper functions for evaluation>=           *)
fun optimizedBind (x, v, xi) =
  let val loc = find (x, xi)
  in  (loc := v; xi)
  end handle NotFound _ => bind (x, ref v, xi)
(* The behavior of a uSmalltalk [[return]], described by *)
(* form \nomathbreak<e, \dots> \returns\usmevalret['] v  *)
(* \aframe', is represented by an ML computation that *)
(* raises the ML [[Return]] exception, again writing *)
(* sigma' and \usedframes' as a side effect. The *)
(* [[Return]] exception is defined here:        *)
(* <definition of the [[Return]] exception>=    *)
exception Return of { value : value, to : frame, unwound : active_send list }
(* Fields [[value]] and [[to]] hold v and \aframe. And *)
(* in the unhappy event that a block tries to return *)
(* after its frame has died, field [[unwound]] is used *)
(* to print diagnostics.                        *)

(* <definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk>= *)
fun eval (e, rho, superclass, F, xi) =
  let val go = applyCheckingOverflow id in go end (* OMIT *)
  let (* <definition of function [[evalMethod]]>=     *)
      fun evalMethod ({ name, superclass, formals, locals, body }, receiver, vs,
                                                                         Fhat) =
            let val ivars  = instanceVars receiver
                val args   = mkEnv (formals, map ref vs)
                val locals = mkEnv (locals,  map (fn _ => ref nilValue) locals)
            in  eval (body, ivars <+> args <+> locals, superclass, Fhat, xi)
            end
            handle BindListLength => raise InternalError
                                             "bad arity in user method" (*OMIT*)
      (* The second part of the \rulenameSend rule is *)
      (* implemented by function [[evalMethod]]. Function *)
      (* [[evalMethod]] computes rho_i as [[ivars]], rho_a as  *)
      (* [[args]], and rho_l as [[locals]]. It also allocates *)
      (* and initializes locations \ldotsn l and \ldotskl', *)
      (* then calls [[eval]].                         *)
      (* <boxed values 3>=                            *)
      val _ = op evalMethod   : method * value * value list * frame -> value
      (* [*]                                          *)

      (* Evaluating returns and sends                 *)
      (*                                              *)
      (* To interpret [[RETURN]], we evaluate the expression *)
      (* to be returned, then return its value to frame [[F]], *)
      (* by raising the [[Return]] exception.         *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
      fun ev (RETURN e) = raise Return { value = ev e, to = F, unwound = [] }
      (* That [[Return]] exception is caught by the code that *)
      (* interprets message send. This code carries a lot of *)
      (* freight, implementing most of rules \stdbreak \ *)
      (* rulenameSend, \rulenameSendSuper, \rulenameReturnTo, *)
      (* and \rulenameReturnPast. All these rules follow the *)
      (* same outline, so here, for reference, is \rulename *)
      (* Send, with the first part highlighted: Each [[SEND]] *)
      (* rule begins in the same way: evaluate the receiver *)
      (* and the arguments using [[ev]], then use the syntax *)
      (* of the receiver to identify the class on which method *)
      (* search begins. Message send dispatches on the *)
      (* receiver, which is used to find the method that *)
      (* defines [[message]], except when the message is sent *)
      (* to [[super]], in which case we use the [[superclass]] *)
      (* of the currently running method. At that point, *)
      (* because of tracing and returns, things start to get *)
      (* complicated, so let's look at the code, then focus on *)
      (* the function passed to [[trace]]: [*]        *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (SEND (srcloc, receiver, msgname, args))  =
            let val obj as (class, rep) = ev receiver
                val vs = map ev args
                val _ = if logging then logSend srcloc msgname else () (*OMIT*)
                val startingClass = case receiver of SUPER => superclass | _ =>
                                                                           class
                val checkpoint = checkpointLimit ()  (*OMIT*)
                (* Evaluation tracing                           *)
                (*                                              *)
                (* The [[trace]] function is given an [[action]] with *)
                (* which to perform the send; [[action]] is run by *)
                (* applying to the empty tuple. If tracing is enabled, *)
                (* [[trace]] emits two tracing messages: one before and *)
                (* one after running the action. The job of knowing *)
                (* whether tracing is enabled, and of emitting \stdbreak *)
                (* messages if so, is delegated to functions    *)
                (* [[traceIndent]] and [[traceOutdent]], each of which *)
                (* takes a tracing action of the form \monoboxfn () => *)
                (* ..., which is executed only if tracing is enabled. *)
                (* <definition of function [[trace]]>=          *)
                fun trace action =
                  let val (file, line) = srcloc
                      val () = 
                        traceIndent (msgname, (file, line)) xi (fn () =>
                          let val c   = className startingClass
                              val obj = if String.isPrefix "class " c then c
                                        else "an object of class " ^ c
                          in  [file, ", line ", intString line, ": ",
                               "Sending message (", spaceSep (msgname :: map
                                                           valueString vs), ")",
                               " to ", obj]
                          end)
                      fun traceOut answer =
                        answer before
                        outdentTrace xi (fn () =>
                           [file, ", line ", intString line, ": ",
                            "(", spaceSep (msgname :: map valueString (obj :: vs
                                                                        )), ")",
                            " = ", valueString answer])

                      fun traceReturn r =
                        ( outdentTrace xi (fn () =>
                             [file, ", line ", intString line, ": ",
                              "(", spaceSep (msgname :: map valueString (obj ::
                                                                      vs)), ")",
                              " terminated by return"])
                        ; raise Return r
                        )

                  in  traceOut (action ()) handle Return r => traceReturn r
                  end
            in  trace
                (fn () =>
                   let val imp = findMethod (msgname, startingClass)
                       val Fhat = newFrame ()
                   in  evalMethod (imp, obj, vs, Fhat)
                       handle Return { value = v, to = F', unwound = unwound }
                                                                              =>
                         if F' = Fhat then
                           v
                           before restoreLimit checkpoint (*OMIT*)
                         else

(* <reraise [[Return]], adding [[msgname]], [[class]], and [[loc]] to [[unwound]]>= *)
                           let val this = { method = msgname, class = className
                                                           class, loc = srcloc }
                           in  raise Return { value = v, to = F', unwound = this
                                                                    :: unwound }
                           end
                   end)
            end
      (* Allocating and evaluating blocks             *)
      (*                                              *)
      (* When a [[BLOCK]] form is evaluated, it captures the *)
      (* current environment, superclass, and stack frame in a *)
      (* closure.                                     *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (BLOCK (formals, body)) = mkBlock (formals, body, rho, superclass,
                                                                              F)
      (* Evaluating value and literal nodes           *)
      (*                                              *)
      (* A [[VALUE]] node stands for itself.          *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (VALUE v) = v
      (* Most [[VALUE]] nodes are created internally, e.g., by *)
      (* the read-eval-print loop when it wants to send *)
      (* [[print]] to an object. Literal numbers and symbols *)
      (* are represented by [[LITERAL]] nodes. When we see *)
      (* one, we call [[mkInteger]] or [[mkSymbol]] to build *)
      (* the literal. It is unsafe to call these functions *)
      (* until we have read the initial basis and bootstrapped *)
      (* the interpreter (\crefsmall.bootstrapping-literals); *)
      (* integer or symbol literals in the initial basis had *)
      (* better appear only inside method definitions. \ *)
      (* stdbreak Evaluating such a literal calls     *)
      (* [[mkInteger]] or [[mkSymbol]], and if you revisit *)
      (* chunks [->] and [->], you will see that it is safe to *)
      (* call [[mkInteger]] only after the interpreter is *)
      (* fully initialized.                           *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (LITERAL c) = 
            (case c of NUM n => mkInteger n
                     | SYM s => mkSymbol s
                     | _ => raise InternalError "unexpected literal")
      (* Reading and writing variables                *)
      (*                                              *)
      (* The cases for [[VAR]] and [[SET]] are as we would *)
      (* expect, given that we have both local and global *)
      (* environments, just as in Impcore. \stdbreak \stdbreak *)
      (* \stdbreak                                    *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (VAR x) = !(find (x, rho) handle NotFound _ => find (x, xi))
        | ev (SET (x, e)) =
            let val v = ev e
                val cell = find (x, rho) handle NotFound _ => find (x, xi)
            in  cell := v; v
            end 
      (* [[                                           *)
      (* SUPER]], when used as an expression, acts just as *)
      (* [[self]] does.                               *)

      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (SUPER) = ev (VAR "self")
      (* Sequential evaluation                        *)
      (*                                              *)
      (* Evaluation of [[BEGIN]] is as in micro-Scheme. *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, nilValue)
            end
      (* Evaluating primitives                        *)
      (*                                              *)
      (* Evaluating a primitive means finding the primitive on *)
      (* an association list, then applying it to its *)
      (* arguments. The [[value]] primitive calls     *)
      (* [[applyClosure]], which needs a global environment, *)
      (* so a global environment is also supplied.    *)
      (* <function [[ev]], the evaluator proper ((usm))>= *)
        | ev (PRIMITIVE (p, args)) =
            let val f = find (p, primitives)
                        handle NotFound n =>
                          raise RuntimeError ("There is no primitive named " ^ n
                                                                               )
            in  f (map ev args, xi)
            end
(* Evaluating expressions, including dynamic dispatch *)
(*                                              *)
(* Just as in the operational semantics, a uSmalltalk *)
(* expression is evaluated in a context that tells it *)
(* about environments rho and xi, [In the code, the *)
(* Greek letter xi, pronounced ``ksee,'' is spelled *)
(* ``[[xi]].''] a static [[superclass]] to which *)
(* messages to [[super]] are sent, and a [[frame]] which *)
(* is terminated by [[return]]. The states sigma and  *)
(* sigma' represent states of the underlying    *)
(* ML interpreter, and the used-frame set \usedframes is *)
(* stored in a mutable variable, so they are not passed *)
(* explicitly. \usmflabeleval                   *)
(* <boxed values 2>=                            *)
val _ = op eval: exp * value ref env * class * frame * value ref env -> value
val _ = op ev  : exp -> value
  in  ev e
  end
(* <definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk>= *)
fun applyClosure ((formals, body, rho, superclass, frame), vs, xi) =
  eval (BEGIN body, bindList (formals, map ref vs, rho), superclass, frame, xi)
  handle BindListLength => 
      raise RuntimeError ("wrong number of arguments to block; expected " ^
                          "(<block> " ^ valueSelector formals ^ " " ^
                          spaceSep formals ^ ")")
(* Once [[eval]] is defined, [[applyClosureRef]] can be *)
(* initialized properly, to a function that implements *)
(* this rule: [*]                               *)
(* <boxed values 5>=                            *)
val _ = op applyClosure : closure * value list * value ref env -> value
val () = applyClosureRef := applyClosure
(* <definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk>= *)
fun evaldef (d, xi) =
  let fun ev e = eval (e, emptyEnv, objectClass, noFrame, xi)
                 handle Return { value = v, unwound = frames, ... } =>
                   (* <report [[return]] escapes [[frames]]>=      *)
                   if null frames then
                     raise RuntimeError ("tried to (return " ^ valueString v ^
                                           ") from an activation that has died")
                   else
                     raise RuntimeError (
                       "tried to return from an activation that has died:\n  " ^
                                         separate ("", "\n  ") (map
                                                       activeSendString frames))
      val (x, v) =
        case d
          of VAL (name, e)             => (name, ev e)
           | EXP e                     => ("it", ev e)
           | DEFINE (name, args, body) => (name, ev (BLOCK (args, [body])))
           | CLASSD (d as {name, ...}) => (name, newClassObject d xi)
      val xi' = optimizedBind (x, v, xi)
      val _ = saveLiteralClasses xi' handle NotFound _ => ()  (*OMIT*)
(* Here's the code: \usmflabelevaldef           *)
(* <boxed values 6>=                            *)
val _ = op evaldef : def * value ref env -> value ref env * value
val _ = op ev      : exp -> value
  in  (xi', v)
  end
(* Evaluating extended definitions              *)
(*                                              *)
(* Extended definitions are evaluated using the reusable *)
(* code presented in \crefmlscheme.chap. Like   *)
(* micro-Scheme, uSmalltalk works with a single *)
(* top-level environment, which maps each name to a *)
(* mutable location holding a value. \stdbreak  *)
(* ``Processing'' a definition means evaluating it, then *)
(* showing the result by sending [[println]] to the *)
(* defined value. The default [[println]] method calls *)
(* the object's [[print]] method, which you can *)
(* redefine.                                    *)
(* <definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk>= *)
type basis = value ref env
fun processDef (d, xi, interactivity) =
  let val (xi', v) = evaldef (d, xi)
      val _ = if prints interactivity then 
                ignore (eval (SEND (nullsrc, VALUE v, "println", []),
                              emptyEnv, objectClass, noFrame, xi'))
              else
                ()
  in  xi'
  end
fun dump_names basis = app (println o fst) basis  (*OMIT*)
(* The source location [[nullsrc]] identifies the *)
(* [[SEND]] as something generated internally, rather *)
(* than read from a file or a list of strings.  *)

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
(* Unit testing                                 *)
(*                                              *)
(* Unit testing in uSmalltalk looks a little different *)
(* from unit testing in micro-Scheme or uML, but a *)
(* little more like unit testing in \mcl: testing for *)
(* equality requires a call to [[eval]], and    *)
(* if something is wrong with a value, we can't convert *)
(* the value to a string---all we can do with a value is *)
(* print it.                                    *)
(* <definition of [[testIsGood]] for \usmalltalk>= *)
fun testIsGood (test, xi) =
  let fun ev e = eval (e, emptyEnv, objectClass, noFrame, xi)
      fun outcome e = withHandlers (OK o ev) e (ERROR o stripAtLoc)
                      before resetTrace ()
      fun testSimilar (v1, v2) =
        let val areSimilar = ev (SEND (nullsrc, VALUE v1, "=", [VALUE v2]))
        in  eqRep (areSimilar, mkBoolean true)
        end
      fun printsAs v =
        let val (bprint, contents) = bprinter ()
            val _ = withXprinter bprint ev (SEND (nullsrc, VALUE v, "print", [])
                                                                               )
        in  contents ()
        end
      fun valueString _ =
        raise RuntimeError "internal error: called the wrong ValueString"
      (* This thing is not like the others, because printing *)
      (* values must go to standard output.           *)

(* <definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]]>= *)
      fun whatWasExpected (LITERAL (NUM n), _) = printsAs (mkInteger n)
        | whatWasExpected (LITERAL (SYM x), _) = printsAs (mkSymbol x)
        | whatWasExpected (e, OK v) =
            concat [printsAs v, " (from evaluating ", expString e, ")"]
        | whatWasExpected (e, ERROR _) =
            concat ["the result of evaluating ", expString e]

(* <definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]]>= *)
      val cxfailed = "check-expect failed: "
      fun checkExpectPasses (checkx, expectx) =
        case (outcome checkx, outcome expectx)
          of (OK check, OK expect) => 
               (case withHandlers (OK o testSimilar) (check, expect) (ERROR o
                                                                     stripAtLoc)
                  of OK true => true
                   | OK false =>
                       failtest [cxfailed, "expected ", expString checkx, 
                                 " to be similar to ", whatWasExpected (expectx,
                                                                     OK expect),
                                 ", but it's ", printsAs check]
                   | ERROR msg =>
                       failtest [cxfailed, "testing similarity of ", expString
                                                                 checkx, " to ",
                                 expString expectx, " caused error ", msg])
           | (ERROR msg, tried) =>
               failtest [cxfailed, "evaluating ", expString checkx,
                                                          " caused error ", msg]
           | (_, ERROR msg) =>
               failtest  [cxfailed, "evaluating ", expString expectx,
                                                          " caused error ", msg]

(* <definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]]>= *)
      val cafailed = "check-assert failed: "
      fun checkAssertPasses checkx =
        case outcome checkx
          of OK check =>
               eqRep (check, mkBoolean true) orelse
               failtest [cafailed, "expected assertion ", expString checkx,
                         " to hold, but it doesn't"]
           | ERROR msg =>
               failtest [cafailed, "evaluating ", expString checkx,
                                                          " caused error ", msg]

(* <definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]]>= *)
      val cefailed = "check-error failed: "
      fun checkErrorPasses checkx =
            case outcome checkx
              of ERROR _ => true
               | OK check =>
                   failtest [cefailed, "expected evaluating ", expString checkx,
                             " to cause an error, but evaluation produced ",
                             printsAs check]
      (* <definition of [[checkPrintPasses]]>=        *)

      val cpfailed = "check-print failed: "
      fun checkPrintPasses (checkx, s) =
        case outcome checkx 
          of OK check =>
               (case withHandlers (OK o printsAs) check (ERROR o stripAtLoc)
                  of OK s' =>
                       s = s' orelse
                       failtest [cpfailed, "expected \"", s, "\" but got \"", s'
                                                                         , "\""]
                   | ERROR msg =>
                       failtest [cpfailed, "calling print method on ",
                                 expString checkx, " caused error ", msg])
           | ERROR msg =>
               failtest [cpfailed, "evaluating ", expString checkx,
                                                          " caused error ", msg]
      fun passes (CHECK_EXPECT (c, e)) = checkExpectPasses (c, e)
        | passes (CHECK_ASSERT c)      = checkAssertPasses c
        | passes (CHECK_ERROR c)       = checkErrorPasses  c
        | passes (CHECK_PRINT (c, s))  = checkPrintPasses  (c, s)
  in  passes test
  end
(* <shared definition of [[processTests]]>=     *)
fun numberOfGoodTests (tests, rho) =
  foldr (fn (t, n) => if testIsGood (t, rho) then n + 1 else n) 0 tests
fun processTests (tests, rho) =
      reportTestResults (numberOfGoodTests (tests, rho), length tests)
(* <boxed values 91>=                           *)
val _ = op processTests : unit_test list * basis -> unit
(* <shared read-eval-print loop and [[processPredefined]]>= *)
fun processPredefined (def,basis) = 
  processDef (def, basis, noninteractive)
(* When reading definitions of predefined functions, *)
(* there's no interactivity.                    *)
(* <boxed values 37>=                           *)
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
      (* <boxed values 40>=                           *)
      val _ = op errmsg     : string -> unit
      val _ = op processDef : def * basis * interactivity -> basis
      val basis = streamFold processXDef basis xdefs
      val _     = processTests (!unitTests, basis)
(* <boxed values 39>=                           *)
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
(*   IMPLEMENTATIONS OF \USMALLTALK\ PRIMITIVES AND DEFINITION OF [[INITIALBASIS]] *)
(*                                                               *)
(*****************************************************************)

(* Initializing, bootstrapping, and running the *)
(* interpreter                                  *)
(*                                              *)
(* The first entries in the initial basis are the *)
(* primitive classes. Each one needs a metaclass to be *)
(* an instance of. To be faithful to Smalltalk, the *)
(* subclass relationships of the metaclasses should be *)
(* isomorphic to the subclass relationships of the *)
(* classes. This is true for user-defined classes *)
(* created with [[newClassObject]], but on the primitive *)
(* classes, I cheat: the metaclasses for        *)
(* [[UndefinedObject]] and [[Class]] inherit directly *)
(* from [[Class]], not from [[Object]]'s metaclass. *)
(* <implementations of \usmalltalk\ primitives and definition of [[initialBasis]]>= *)
val initialXi = emptyEnv

fun addClass (c, xi) = bind (className c, ref (classObject c), xi)
val initialXi =
  foldl addClass initialXi [ objectClass, nilClass, classClass, metaclassClass ]
(* \makenowebnotdef (from chunk \upshape[->]) The next *)
(* entries are the predefined classes. To help  *)
(* debugging, I define function [[errmsg]] to identify *)
(* an error as originating in a predefined class and to *)
(* use [[eprintlnTrace]] instead of [[eprintln]], so *)
(* that if an error occurs, a stack trace is printed.  *)
(* [*]                                          *)
(* <implementations of \usmalltalk\ primitives and definition of [[initialBasis]]>= *)
val initialXi =
  let val xdefs =
        stringsxdefs ("predefined classes", 
                      
                       [ ";  \\vfilbreak[5000]1.5in                        "
                       , ";                                               "
                       ,
                       ";  Wide interfaces on narrow implementations: Booleans "
                       , ";  and magnitudes                               "
                       , ";                                               "
                       ,
                        ";  [*] An abstract class can provide a wide interface "
                       ,
                     ";  (the full protocol of the abstract class) on a narrow "
                       , ";  foundation (the subclass responsibilities).  "
                       ,
                        ";  To illustrate the technique, I present the Boolean "
                       , ";  classes and the [[Magnitude]] class.         "
                       , ";                                               "
                       , ";  \\vfilbreak[5000]1.5in                        "
                       , ";                                               "
                       , ";  Implementation of Booleans                   "
                       , ";                                               "
                       ,
                        ";  Like Smalltalk-80, uSmalltalk has only two control "
                       , ";  structures: message passing and [[return]]. The "
                       ,
                        ";  syntax has no conditional forms and no loop forms. "
                       , ";  Instead, conditionals are implemented by sending "
                       , ";  continuations to Boolean objects, and loops are "
                       , ";  implemented by sending continuations to block "
                       ,
                      ";  objects. [This implementation of conditionals is the "
                       , ";  same one used in the \\emph{Church encoding} of "
                       ,
                     ";  Booleans in the \\emph{lambda calculus}---a~tool used "
                       ,
                       ";  in the theoretical study of programming languages.] "
                       , ";  The same Boolean objects that support        "
                       , ";  continuation-passing conditionals also support "
                       , ";  classic Boolean operations. \\stdbreak[5000]  "
                       ,
                      ";  The entire Boolean protocol is implemented on top of "
                       ,
                     ";  the single method [[ifTrue:ifFalse:]], which is class "
                       , ";  [[Boolean]]'s only subclass responsibility. [*] "
                       , ";                                               "
                       , ";  <predefined uSmalltalk classes and values>= "
                       , "(class Boolean "
                       , "    [subclass-of Object]"
                       ,
"    (method ifTrue:ifFalse: (trueBlock falseBlock) (self subclassResponsibility))"
                       , "  "
                       , "    (method ifFalse:ifTrue: (falseBlock trueBlock) "
                       , "        (self ifTrue:ifFalse: trueBlock falseBlock))"
                       ,
        "    (method ifTrue:  (trueBlock)  (self ifTrue:ifFalse: trueBlock {}))"
                       ,
       "    (method ifFalse: (falseBlock) (self ifTrue:ifFalse: {} falseBlock))"
                       , "    "
                       ,
   "    (method not ()          (self ifTrue:ifFalse: {false}          {true}))"
                       ,
"    (method eqv: (aBoolean) (self ifTrue:ifFalse: {aBoolean}       {(aBoolean not)}))"
                       ,
"    (method xor: (aBoolean) (self ifTrue:ifFalse: {(aBoolean not)} {aBoolean}))"
                       , ""
                       ,
            "    (method & (aBoolean) (self ifTrue:ifFalse: {aBoolean} {self}))"
                       ,
            "    (method | (aBoolean) (self ifTrue:ifFalse: {self} {aBoolean}))"
                       , "  "
                       ,
"    (method and: (alternativeBlock) (self ifTrue:ifFalse: alternativeBlock {self}))"
                       ,
"    (method or:  (alternativeBlock) (self ifTrue:ifFalse: {self} alternativeBlock))"
                       , ")"
                       ,
                        ";  Like [[isNil]] and [[notNil]], [[ifTrue:ifFalse:]] "
                       , ";  does case analysis using method dispatch. Classes "
                       ,
                       ";  [[True]] and [[False]] have a single instance each: "
                       ,
                        ";  an object [[true]] of class [[True]] and an object "
                       ,
                     ";  [[false]] of class [[False]]. \\stdbreak One of these "
                       ,
                       ";  objects is answered by every Boolean-valued method, "
                       , ";  and therefore, the [[ifTrue:ifFalse:]] message is "
                       ,
                       ";  sent only to these objects. \\stdbreak To implement "
                       , ";  conditional control, we simply define the    "
                       , ";  [[ifTrue:ifFalse:]] method differently in each "
                       , ";  subclass. [*]                                "
                       , ";  <predefined uSmalltalk classes and values>= "
                       , "(class True "
                       , "  [subclass-of Boolean]"
                       ,
           "  (method ifTrue:ifFalse: (trueBlock falseBlock) (trueBlock value))"
                       , ")"
                       , "(class False"
                       , "  [subclass-of Boolean]"
                       ,
          "  (method ifTrue:ifFalse: (trueBlock falseBlock) (falseBlock value))"
                       , ")"
                       , ";  Implementation of blocks                     "
                       , ";                                               "
                       , ";  A block is an abstraction of a function, and its "
                       ,
                      ";  representation is primitive. The [[value]] method is "
                       ,
                     ";  also primitive,[*] but the [[while]], [[whileTrue:]], "
                       , ";  and [[whileFalse:]] methods are easily defined in "
                       , ";  ordinary uSmalltalk.                         "
                       , ";  <predefined uSmalltalk classes and values>= "
                       , "(class Block"
                       , "    [subclass-of Object] ; internal representation"
                       , "    (class-method new () {})"
                       ,
    "    (method value                    ()            (primitive value self))"
                       ,
 "    (method value:                   (a1)          (primitive value self a1))"
                       ,
"    (method value:value:             (a1 a2)       (primitive value self a1 a2))"
                       ,
"    (method value:value:value:       (a1 a2 a3)    (primitive value self a1 a2 a3))"
                       ,
"    (method value:value:value:value: (a1 a2 a3 a4) (primitive value self a1 a2 a3 a4))"
                       , "    (method whileTrue: (body)"
                       , "        ((self value) ifTrue:ifFalse:"
                       , "            {(body value)"
                       , "             (self whileTrue: body)}"
                       , "            {nil}))"
                       , "    (method whileFalse: (body) "
                       , "         ((self value) ifTrue:ifFalse:"
                       , "             {nil}"
                       , "             {(body value) "
                       , "              (self whileFalse: body)}))"
                       , ")"
                       ,
                      ";  There is no need to create [[Symbol]] internally, so "
                       , ";  we put it in the initial basis.              "
                       , ";  <predefined uSmalltalk classes and values>= "
                       , "(class Symbol"
                       , "    [subclass-of Object] ; internal representation"
                       ,
            "    (class-method new  () (self error: 'can't-send-new-to-Symbol))"
                       ,
          "    (class-method new: (aSymbol) (primitive newSymbol self aSymbol))"
                       ,
                     "    (method       print  () (primitive printSymbol self))"
                       , "    (method       hash   () (primitive hash self))"
                       , ")"
                       , ";  <predefined uSmalltalk classes and values>= "
                       , "(class CompiledMethod"
                       , "  [subclass-of Object]"
                       , ")"
                       ,
                     ";  The numeric and collection classes are in the initial "
                       , ";  basis.                                       "
                       , ";  <predefined uSmalltalk classes and values>= "
                       , ";  Implementation of magnitudes                 "
                       , ";                                               "
                       ,
                      ";  Like class [[Boolean]], class [[Magnitude]] provides "
                       , ";  a relatively big protocol over a small set of "
                       , ";  subclass responsibilities. The big [[Magnitude]] "
                       ,
                     ";  protocol is suited to any abstraction that is totally "
                       ,
                      ";  ordered but does not necessarily support arithmetic: "
                       , ";  \\stdbreak numbers, dates, times, and so on.  "
                       , ";  An implementation has only two responsibilities: "
                       ,
                       ";  comparisons [[=]] and [[<]]. The other comparisons, "
                       , ";  as well as [[min:]] and [[max:]], are implemented "
                       , ";  using [[<]].                                 "
                       , ";  <numeric classes>=                           "
                       , "(class Magnitude"
                       , "    [subclass-of Object] ; abstract class"
                       ,
"    (method =  (x) (self subclassResponsibility)) ; may not inherit from Object"
                       , "    (method <  (x) (self subclassResponsibility))"
                       , "    (method >  (y) (y < self))"
                       , "    (method <= (x) ((self > x) not))"
                       , "    (method >= (x) ((self < x) not))"
                       ,
"    (method min: (aMagnitude) ((self < aMagnitude) ifTrue:ifFalse: {self} {aMagnitude}))"
                       ,
"    (method max: (aMagnitude) ((self > aMagnitude) ifTrue:ifFalse: {self} {aMagnitude}))"
                       , ")"
                       , ";  <numeric classes ((elided))>=                "
                       , ";  Class Number, plus powers and roots          "
                       , ";                                               "
                       ,
                        ";  If an object supports not just comparison but also "
                       , ";  arithmetic, it's a number. [[Number]] is also an "
                       , ";  abstract class; any subclass must supply four "
                       ,
                       ";  arithmetic operations and four conversions, as well "
                       , ";  as the [[=]] and [[<]] methods required by the "
                       , ";  [[Magnitude]] protocol.                      "
                       , ";  <definition of class [[Number]]>=            "
                       , "(class Number"
                       , "    [subclass-of Magnitude]  ; abstract class"
                       , "    ;;;;;;; basic Number protocol"
                       ,
                  "    (method +   (aNumber)     (self subclassResponsibility))"
                       ,
                  "    (method *   (aNumber)     (self subclassResponsibility))"
                       ,
                  "    (method negated    ()     (self subclassResponsibility))"
                       ,
                  "    (method reciprocal ()     (self subclassResponsibility))"
                       , "    "
                       ,
                  "    (method asInteger  ()     (self subclassResponsibility))"
                       ,
                  "    (method asFraction ()     (self subclassResponsibility))"
                       ,
                  "    (method asFloat    ()     (self subclassResponsibility))"
                       ,
                  "    (method coerce: (aNumber) (self subclassResponsibility))"
                       ,
                  ";      As usual, several methods in the [[Number]] protocol "
                       ,
                  ";      are implemented in abstract class [[Number]], on top "
                       ,
                     ";      of the subclass responsibilities. First, from the "
                       ,
                    ";      inverse operations [[negated]] and [[reciprocal]], "
                       ,
                        ";      we get binary subtraction, absolute value, and "
                       , ";      division.                                    "
                       , ";      <other methods of class [[Number]]>=         "
                       , "    (method -   (y) (self + (y  negated)))"
                       ,
"    (method abs ()  ((self isNegative) ifTrue:ifFalse: {(self  negated)} {self}))"
                       , "    (method /   (y) (self * (y reciprocal)))"
                       ,
                  ";      Next, from the comparisons and coercions, we get the "
                       ,
                   ";      sign predicates, which are implemented by comparing "
                       ,
                 ";      [[self]] with zero. The implementations also show how "
                       , ";      to use the [[coerce:]] method.               "
                       , ";      <other methods of class [[Number]]>=         "
                       ,
                 "    (method isNegative         () (self  < (self coerce: 0)))"
                       ,
                 "    (method isNonnegative      () (self >= (self coerce: 0)))"
                       ,
                 "    (method isStrictlyPositive () (self  > (self coerce: 0)))"
                       ,
                        ";      The implementation of [[squared]] is easy. The "
                       ,
                   ";      implementation of [[raisedToInteger:]] computes x^n "
                       ,
                      ";      using a standard algorithm that requires O(logn) "
                       ,
                    ";      multiplications. The algorithm has two base cases, "
                       , ";      for x^0 and x^1.                             "
                       , ";      <other methods of class [[Number]]>=         "
                       , "    (method squared () (self * self))"
                       , "    (method raisedToInteger: (anInteger)"
                       , "        ((anInteger = 0) ifTrue:ifFalse:"
                       , "            {(self coerce: 1)}"
                       , "            {((anInteger = 1) ifTrue:ifFalse: {self}"
                       ,
      "                {(((self raisedToInteger: (anInteger div: 2)) squared) *"
                       ,
          "                    (self raisedToInteger: (anInteger mod: 2)))})}))"
                       , ";      [*] Our implementation of square root uses   "
                       , ";      Newton-Raphson iteration. Given input n, this "
                       ,
                   ";      algorithm uses an initial approximation x_0 = 1 and "
                       , ";      improves it stepwise. At step i, the improved "
                       ,
                  ";      approximation is x_i = (x_i-1 + n/x_i-1) /2. To know "
                       , ";      when to stop improving, we need a convergence "
                       ,
                 ";      condition, which examines x_i and x_i-1 and says when "
                       ,
                  ";      they are close enough to accept x_i as the answer. [ "
                       ,
               ";      The idea is that if $x_{i} \\approx x_{i-1}$, \\( x_{i} "
                       ,
                ";      = (x_{i-1} + n/x_{i-1}) / 2 \\approx (x_{i} + n/x_{i}) "
                       ,
              ";      / 2 \\), and solving yields $x_{i} \\approx \\sqrt{n}$.] "
                       ,
                   ";      Our convergence condition is |x_i-x_i-1| < epsilon. "
                       ,
                  ";      The default epsilon used in [[sqrt]] is 1/1000 Using "
                       ,
                      ";      [[coerce:]] ensures we can use the same [[sqrt]] "
                       , ";      method for both fractions and floats.        "
                       , ";      <other methods of class [[Number]]>=         "
                       ,
             "    (method sqrt () (self sqrtWithin: (self coerce: (1 / 1000))))"
                       ,
                    "    (method sqrtWithin: (epsilon) [locals two x<i-1> x<i>]"
                       , "        ; find square root of receiver within epsilon"
                       , "        (set two    (self coerce: 2))"
                       , "        (set x<i-1> (self coerce: 1))"
                       ,
                       "        (set x<i>   ((x<i-1> + (self / x<i-1>)) / two))"
                       ,
                       "        ({(((x<i-1> - x<i>) abs) > epsilon)} whileTrue:"
                       , "               {(set x<i-1> x<i>)"
                       ,
               "                (set x<i> ((x<i-1> + (self / x<i-1>)) / two))})"
                       , "        x<i>)"
                       , ")"
                       ,
                     ";  An object of class [[Fraction]] represents a rational "
                       ,
                       ";  number. The representation is a fraction; numerator "
                       ,
                      ";  [[num]] and denominator [[den]] are integer instance "
                       , ";  variables. The abstraction function maps this "
                       , ";  representation to the ratio fracnumden.      "
                       ,
                        ";  The representation invariant is that the numerator "
                       , ";  and denominator are in reduced form: (1) if the "
                       ,
                        ";  number is zero, the denominator is one; (2) if the "
                       ,
                       ";  number is nonzero, the denominator is positive; (3) "
                       ,
                      ";   the numerator and denominator are reduced to lowest "
                       , ";  terms, that is, their only common divisor is one. "
                       , ";  These conditions ensure that a reduced form is "
                       ,
                       ";  unique: two [[Fraction]] objects represent the same "
                       ,
                      ";  fraction if and only if they have the same numerator "
                       ,
                        ";  and denominator. \\stdbreak[5000] The reduced-form "
                       , ";  invariants are established by private methods "
                       ,
                      ";  [[divReduce]] and [[signReduce]]. When a fraction is "
                       ,
                       ";  created via class method [[num:den:]], both private "
                       , ";  methods are used:                            "
                       , ";  <numeric classes>=                           "
                       , "(class Fraction"
                       , "    [subclass-of Number]"
                       , "    [ivars num den]"
                       ,
               "    (class-method num:den: (a b) ((self new) initNum:den: a b))"
                       , "    (method initNum:den: (a b) ; private"
                       , "        (self setNum:den: a b)"
                       , "        (self signReduce)"
                       , "        (self divReduce))"
                       ,
         "    (method setNum:den: (a b) (set num a) (set den b) self) ; private"
                       ,
                  ";      As discussed in \\crefpagesmall.inspecting-multiple, "
                       , ";      a binary arithmetic operation needs access to "
                       , ";      representation of its argument as well as its "
                       , ";      receiver. Access to the representation of a  "
                       ,
                       ";      [[Fraction]] is provided by the private methods "
                       , ";      [[num]] and [[den]].                         "
                       , ";      <other methods of class [[Fraction]]>=       "
                       , "    (method num () num)  ; private"
                       , "    (method den () den)  ; private"
                       ,
                  ";      First, comparisons. Because fractions are in reduced "
                       ,
                    ";      form, two fractions are equal if and only if their "
                       ,
                  ";      numerators and denominators are equal; no arithmetic "
                       , ";      is required. The [[<]] comparison requires   "
                       ,
                  ";      multiplication; fracnd < fracn'd' if and only if n\\ "
                       , ";      atimesd' < n'\\atimesd.                       "
                       , ";      <other methods of class [[Fraction]]>=       "
                       ,
                   "    (method = (f) ((num = (f num)) and: {(den = (f den))}))"
                       ,
                        "    (method < (f) ((num * (f den)) < ((f num) * den)))"
                       ,
                   ";      Next, arithmetic. Multiplication uses the algebraic "
                       ,
              ";      law fracnd\\atimesfracn'd' = fracn\\atimesn'd\\atimesd'. "
                       ,
                 ";      The numerator n\\atimesn' and denominator d\\atimesd' "
                       , ";      can have common factors, so [[divReduce]] is "
                       ,
                     ";      necessary, but d\\atimesd' cannot be negative, so "
                       , ";      [[signReduce]] is not necessary.             "
                       , ";      <other methods of class [[Fraction]]>=       "
                       , "    (method * (f)"
                       ,
"        (((Fraction new) setNum:den: (num * (f num)) (den * (f den))) divReduce))"
                       ,
                    ";      The simplest implementation of [[+]] would use the "
                       ,
                ";      algebraic law fracnd + fracn'd' = fracn\\atimesd'+n'\\ "
                       ,
                        ";      atimesdd\\atimesd', then call [[divReduce]] to "
                       ,
                  ";      eliminate common factors (e.g., frac12+frac12 = frac "
                       ,
                     ";      44 = frac1 1). But the computation of d\\atimesd' "
                       ,
                        ";      might overflow. I make overflow less likely by "
                       ,
                   ";      defining temp = lcm(d, d'), putting [[temp]] in the "
                       ,
                    ";      denominator, and using fractempd and fractempd' as "
                       , ";      needed. Without this tweak, the square-root  "
                       , ";      computations in Section [->] would overflow. "
                       ,
                        ";      If needed, a similar tweak could be applied to "
                       , ";      multiplication.                              "
                       , ";      <other methods of class [[Fraction]]>=       "
                       , "    (method + (f) [locals temp]"
                       , "        (set temp (den lcm: (f den)))"
                       , "        (((Fraction new) setNum:den:"
                       ,
"                         ((num * (temp div: den)) + ((f num) * (temp div: (f den))))"
                       , "                         temp)"
                       , "            divReduce))"
                       ,
                      ";      The remaining methods, including [[reciprocal]], "
                       ,
                    ";      [[print]], and the coercions, are relegated to the "
                       ,
                 ";      Supplement. Except the sign tests, which are too cute "
                       ,
                     ";      to omit: because of the representation invariant, "
                       ,
                  ";      a sign test on a fraction is implemented by applying "
                       , ";      the same sign test to its numerator.         "
                       , ";      <other methods of class [[Fraction]]>=       "
                       , "    (method isNegative         () (num isNegative))"
                       ,
                        "    (method isNonnegative      () (num isNonnegative))"
                       ,
                   "    (method isStrictlyPositive () (num isStrictlyPositive))"
                       , ";      Selected methods of class Fraction           "
                       , ";                                                   "
                       ,
                 ";      Each of the other arithmetic operations calls at most "
                       ,
                  ";      one of these methods, depending upon what invariants "
                       , ";      the operation might violate. For example, if "
                       ,
                   ";      [[negate]]'s receiver is in reduced form, so is its "
                       ,
                       ";      result. Method [[negate]] therefore violates no "
                       ,
                     ";      invariants, and it needn't call [[signReduce]] or "
                       ,
                  ";      [[divReduce]]. \\stdbreak As another example, if two "
                       ,
                     ";      fractions in reduced form are added, the result's "
                       ,
                        ";      denominator is not negative, because it is the "
                       ,
                      ";      product of two nonnegative denominators, but the "
                       , ";      result's numerator and denominator may have a "
                       ,
                      ";      nontrivial common divisor, so invariant 3 may be "
                       , ";      violated. The [[+]] method therefore calls   "
                       ,
                       ";      [[divReduce]]. A similar argument applies to *. "
                       , ";      <other methods of class [[Fraction]]>=       "
                       , "    (method signReduce () ; private"
                       , "        ((den isNegative) ifTrue:"
                       ,
                "            {(set num (num negated)) (set den (den negated))})"
                       , "        self)"
                       , ""
                       , "    (method divReduce () [locals temp] ; private"
                       , "        ((num = 0) ifTrue:ifFalse:"
                       , "            {(set den 1)}"
                       , "            {(set temp ((num abs) gcd: den))"
                       , "             (set num  (num div: temp))"
                       , "             (set den  (den div: temp))})"
                       , "        self)"
                       ,
                   ";      Like method [[setNum:den:]], methods [[signReduce]] "
                       ,
                   ";      and [[divReduce]] answer [[self]]. This convention, "
                       ,
                       ";      which is common in object-oriented programming, "
                       ,
                      ";      simplifies the implementations of the arithmetic "
                       , ";      operations.                                  "
                       , ""
                       ,
                        ";      Negation simply negates the numerator. Because "
                       ,
                  ";      numbers are immutable, we return a new fraction with "
                       , ";      the negated numerator.                       "
                       , ";      <other methods of class [[Fraction]]>=       "
                       ,
        "    (method negated () ((Fraction new) setNum:den: (num negated) den))"
                       ,
                    ";      Instead of simply calling \\mono(Fraction num:den: "
                       ,
                  ";      (num negated) den), we call [[setNum:den:]] on a new "
                       , ";      fraction. By avoiding [[num:den:]], we avoid "
                       , ";      unnecessary calls to [[divReduce]] and       "
                       ,
                 ";      [[signReduce]], doing only what is needed to maintain "
                       , ";      the representation invariant.                "
                       , ""
                       ,
                    ";      The method [[reciprocal]] inverts a fraction. This "
                       ,
                 ";      operation leaves a positive fraction in reduced form, "
                       ,
                     ";      but it leaves a negative fraction with a negative "
                       ,
                 ";      denominator. \\stdbreak Sending [[signReduce]] to the "
                       ,
                 ";      inverted fraction sets things right regardless of the "
                       ,
                  ";      original sign. (The reciprocal of zero cannot be put "
                       ,
                     ";      into reduced form. Nothing can be done about it.) "
                       , ";      <other methods of class [[Fraction]]>=       "
                       , "    (method reciprocal ()"
                       ,
                     "       (((Fraction new) setNum:den: den num) signReduce))"
                       ,
                    ";      The [[print]] method for fractions shows numerator "
                       , ";      and denominator.                             "
                       , ";      <other methods of class [[Fraction]]>=       "
                       ,
                 "    (method print () (num print) ('/ print) (den print) self)"
                       ,
                 ";      Here are the conversions. Like an integer, a fraction "
                       ,
                   ";      knows how to convert itself to a value of any other "
                       ,
                 ";      numeric class. The knowledge of how to do the inverse "
                       ,
                  ";      conversion, from a value of another numeric class to "
                       , ";      a fraction, lies the other class, in its     "
                       , ";      implementation of [[asFraction]].            "
                       , ";      <other methods of class [[Fraction]]>=       "
                       , "    (method asInteger  () (num div: den))"
                       ,
                    "    (method asFloat    () ((num asFloat) / (den asFloat)))"
                       , "    (method asFraction () self)"
                       , "    (method coerce: (aNumber) (aNumber asFraction))"
                       , ";      Converting a fraction to an integer may lose "
                       , ";      precision.                                   "
                       , ""
                       , ")"
                       , ";  A natural number is represented as a sequence of "
                       , ";  digits in some base b. As explained in \\cref "
                       ,
                        ";  mcl.bignums, the sequence may be represented as an "
                       ,
                        ";  array or as a list. \\stdbreak I recommend against "
                       ,
                     ";  using uSmalltalk's predefined class [[List]]; you are "
                       , ";  better off defining empty and nonempty lists of "
                       ,
                     ";  digits as subclasses of class [[Natural]]. \\stdbreak "
                       ,
                       ";  For this reason, I refer to the two representations "
                       ,
                        ";  as the ``array representation'' and the ``subclass "
                       ,
                    ";  representation.'' \\stdbreak Each representation comes "
                       , ";  with its own private protocol, which is used to "
                       , ";  implement the complex methods. \\stdbreak And no "
                       ,
                     ";  matter which representation you choose, you can start "
                       ,
                    ";  with the template in \\crefsmall.fig.Natural-template. "
                       , ";                                               "
                       , ";  \\stdbreak[3000]                              "
                       , ";                                               "
                       ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                       , ";  <numeric classes>=                           "
                       , "(class Natural"
                       , "   [subclass-of Magnitude]"
                       , "   ; instance variables left as an exercise"
                       , ""
                       ,
                "   (class-method fromSmall: (anInteger) (self leftAsExercise))"
                       , ""
                       , "   (method = (aNatural) (self leftAsExercise))"
                       , "   (method < (aNatural) (self leftAsExercise))"
                       , ""
                       , "   (method + (aNatural) (self leftAsExercise))"
                       , "   (method * (aNatural) (self leftAsExercise))"
                       ,
     "   (method - (aNatural) (self subtract:withDifference:ifNegative aNatural"
                       ,
"                          {(self error: 'Natural-subtraction-went-negative)}))"
                       ,
             "   (method subtract:withDifference:ifNegative (aNatural exnBlock)"
                       , "                        (self leftAsExercise))"
                       , ""
                       ,
                  "   (method sdiv: (n) (self sdivmod:with: n [block (q r) q]))"
                       ,
                  "   (method smod: (n) (self sdivmod:with: n [block (q r) r]))"
                       ,
                    "   (method sdivmod:with: (n aBlock) (self leftAsExercise))"
                       , ""
                       , "   (method decimal () (self leftAsExercise))"
                       , "   (method isZero  () (self leftAsExercise))"
                       , ""
                       ,
             "   (method print   () ((self decimal) do: [block (x) (x print)]))"
                       , ")"
                       , ";  Integer division and modulus are defined only on "
                       , ";  integers, as are greatest common denominator and "
                       , ";  least common multiple.                       "
                       , ";  <numeric classes>=                           "
                       , "(class Integer"
                       , "    [subclass-of Number] ; abstract class"
                       , "    (method div: (n) (self subclassResponsibility))"
                       , "    (method mod: (n) (self - (n * (self div: n))))"
                       ,
"    (method gcd: (n) ((n = (self coerce: 0)) ifTrue:ifFalse: {self} {(n gcd: (self mod: n))}))"
                       , "    (method lcm: (n) (self * (n div: (self gcd: n))))"
                       , ";      Interoperation among numbers: Abstract class "
                       , ";      [[Integer]]                                  "
                       , ";                                                   "
                       ,
                      ";      Integers interoperate with other numeric classes "
                       ,
                   ";      primarily through conversions: Each class of number "
                       ,
                    ";      knows how to coerce itself to every other class of "
                       ,
                ";      number. \\stdbreak Each class therefore implements the "
                       ,
                        ";      [[asFraction]], [[asFloat]], and [[asInteger]] "
                       ,
                       ";      methods. \\stdbreak To implement these methods, "
                       ,
                   ";      a class has to know not only its own representation "
                       ,
                    ";      and methods, but what methods of the other numeric "
                       ,
                     ";      classes are needed to create a number. \\stdbreak "
                       ,
                 ";      For example, the [[Integer]] class needs to know what "
                       ,
                  ";      methods of classes [[Fraction]] and [[Float]] to use "
                       ,
                    ";      to create an equivalent [[Fraction]] (class method "
                       , ";      [[num:den:]]) or [[Float]] (class method     "
                       , ";      [[mant:exp:]]).                              "
                       , ";      <other methods of class [[Integer]]>=        "
                       ,
                        "    (method asFraction () (Fraction  num:den: self 1))"
                       ,
                        "    (method asFloat    () (Float mant:exp:    self 0))"
                       , "    (method asInteger  () self)"
                       ,
                 ";      Just as it's up to [[Integer]] to know how to convert "
                       ,
                    ";      itself to another kind of number, it's up to other "
                       ,
                 ";      kinds of numbers to know how to convert themselves to "
                       ,
                       ";      integers. Thus, the [[coerce:]] method on class "
                       ,
                     ";      [[Integer]] simply delegates to the [[asInteger]] "
                       , ";      method of the argument.                      "
                       , ""
                       , ";      <other methods of class [[Integer]]>=        "
                       , "    (method coerce: (aNumber) (aNumber asInteger))"
                       ,
                   ";      Integers interoperate with other numeric classes in "
                       ,
                    ";      one other way: division. When integers are divided "
                       ,
                      ";      using the standard method [[/]], the result is a "
                       , ";      fraction.                                    "
                       , ";      <other methods of class [[Integer]]>=        "
                       ,
                        "    (method reciprocal () (Fraction num:den: 1 self)) "
                       ,
                        "    (method / (aNumber) ((self asFraction) / aNumber))"
                       ,
                 ";      The integer method [[timesRepeat:]] executes a loop a "
                       , ";      finite number of times.                      "
                       , ";      <other methods of class [[Integer]]>=        "
                       , "    (method timesRepeat: (aBlock) [locals count]"
                       ,
    "        ((self isNegative) ifTrue: {(self error: 'negative-repeat-count)})"
                       , "        (set count self)"
                       , "        ({(count != 0)} whileTrue:"
                       , "             {(aBlock value)"
                       , "              (set count (count - 1))}))"
                       , ")"
                       ,
                     ";  The only concrete integer class built into uSmalltalk "
                       , ";  is [[SmallInteger]]. Almost all its methods are "
                       ,
                       ";  primitive. They are defined in chunks [->]-- [->].  "
                       , ";  [*]                                          "
                       , ";  <numeric classes>=                           "
                       , "(class SmallInteger"
                       , "    [subclass-of Integer] ; primitive representation"
                       ,
                "    (class-method new: (n) (primitive newSmallInteger self n))"
                       , "    (class-method new  ()  (self new: 0))"
                       , "    (method negated    ()  (0 - self))"
                       ,
                "    (method print      ()  (primitive printSmallInteger self))"
                       , "    (method +          (n) (primitive + self n))"
                       , "    (method -          (n) (primitive - self n))"
                       , "    (method *          (n) (primitive * self n))"
                       , "    (method div:       (n) (primitive div self n))"
                       ,
                     "    (method =          (n) (primitive sameObject self n))"
                       , "    (method <          (n) (primitive < self n))"
                       , "    (method >          (n) (primitive > self n))"
                       , ")"
                       ,
                      ";  The primitives don't support mixed arithmetic, e.g., "
                       ,
                      ";  comparison of integers and fractions. Writing better "
                       , ";  methods is a task you can do in \\crefpage    "
                       , ";  small.ex.mixed-arithmetic.                   "
                       , ""
                       ,
                       ";  An object of class [[Float]] is an abstraction of a "
                       ,
                       ";  rational number. The representation is an integer m "
                       , ";  (the mantissa) combined with an integer e (the  "
                       ,
                      ";  exponent), stored in instance variables [[mant]] and "
                       ,
                    ";  [[exp]]. \\stdbreak The abstraction function maps this "
                       ,
                   ";  representation to the number \\nomathbreakm\\atimes10^e "
                       , ";  . Both m and e can be negative. \\stdbreak    "
                       , ";  The representation invariant guarantees that the "
                       ,
                     ";  absolute value of the mantissa is at most 2^15-1. The "
                       ,
                      ";  invariant ensures that we can multiply two mantissas "
                       ,
                    ";  without \\stdbreak overflow, even on an implementation "
                       , ";  that provides only 31-bit small integers. [Some "
                       , ";  implementations of ML reserve one bit as a   "
                       , ";  dynamic-type tag or as a tag for the garbage "
                       ,
                     ";  collector.] The invariant is maintained with the help "
                       ,
                      ";  of a private [[normalize]] method: \\stdbreak when a "
                       , ";  mantissa's magnitude exceeds 2^15-1, the     "
                       ,
                       ";  [[normalize]] method divides the mantissa by 10 and "
                       ,
                       ";  increments the exponent until the mantissa is small "
                       ,
                     ";  enough. \\stdbreak This operation loses precision; it "
                       ,
                      ";  is the source of so-called ``floating-point rounding "
                       ,
                     ";  error.'' \\stdbreak The possibility of rounding error "
                       , ";  implies that the answers obtained \\stdbreak from "
                       , ";  floating-point arithmetic are approximate. This "
                       , ";  possibility is part of the specification of class "
                       , ";  [[Float]], but specifying exactly what       "
                       , ";  ``approximate'' means is beyond the scope of this "
                       , ";  book.                                        "
                       , ";  <numeric classes>=                           "
                       , "(class Float"
                       , "    [subclass-of Number]"
                       , "    [ivars mant exp]"
                       ,
             "    (class-method mant:exp: (m e) ((self new) initMant:exp: m e))"
                       , "    (method initMant:exp: (m e) ; private"
                       , "        (set mant m) (set exp e) (self normalize))"
                       , "    (method normalize ()    ; private"
                       , "        ({((mant abs) > 32767)} whileTrue:"
                       , "               {(set mant (mant div: 10))"
                       , "                (set exp (exp + 1))})"
                       , "        self)"
                       ,
                        ";      Like the other numeric classes, [[Float]] must "
                       ,
                   ";      provide methods that give a binary operation access "
                       , ";      to the representation of its argument.       "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method mant () mant)  ; private"
                       , "    (method exp  () exp)   ; private"
                       ,
                      ";      Comparing two floats with different exponents is "
                       ,
                    ";      awkward, so instead I compute their difference and "
                       ,
                       ";      compare it with zero. For this purpose, I add a "
                       , ";      private method [[isZero]].                   "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method < (x) ((self - x) isNegative))"
                       , "    (method = (x) ((self - x)   isZero))"
                       , "    (method isZero () (mant = 0))  ; private"
                       ,
                   ";      Negation is easy: answer a new float with a negated "
                       , ";      mantissa.                                    "
                       , ";      <other methods of class [[Float]]>=          "
                       ,
                  "    (method negated () (Float mant:exp: (mant negated) exp))"
                       ,
                        ";      The [[+]] method adds x' = m' \\atimes10^e' to "
                       ,
                 ";      [[self]], which is m \\atimes10^e. Its implementation "
                       ,
                  ";      is based on the algebraic law m \\atimes10^e = (m \\ "
                       ,
                        ";      atimes10^e-e') \\atimes10^e'. This law implies "
                       , ";                                                   "
                       ,
                   ";       m \\atimes10^e + m' \\atimes10^e' = (m \\atimes10^ "
                       , ";       e-e' + m') \\atimes10^e'.                    "
                       , ";                                                   "
                       ,
                ";      I provide a naï ve implementation which enforces e-e' "
                       ,
                 ";      >=0. This implementation risks overflow, but at least "
                       ,
                    ";      overflow can be detected. A naï ve implementation "
                       ,
                        ";      using e-e'<=0 might well lose valuable bits of "
                       ,
                      ";      precision from m. A better implementation can be "
                       , ";      constructed using the ideas in Exercise [->]. "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method + (x-prime) "
                       , "        ((exp >= (x-prime exp)) ifTrue:ifFalse:"
                       ,
"            {(Float mant:exp: ((mant * (10 raisedToInteger: (exp - (x-prime exp)))) +"
                       , "                                 (x-prime mant))"
                       , "                              (x-prime exp))}"
                       , "            {(x-prime + self)}))"
                       ,
                   ";      Multiplication is much simpler: (m \\atimes10^e) \\ "
                       ,
                 ";      atimes(m' \\atimes10^e') = (m \\atimesm') \\atimes10^ "
                       ,
                ";      e+e'. The product's mantissa m\\atimesm' may be large, "
                       ,
                     ";      but the class method [[mant:exp:]] normalizes it. "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method * (x-prime) "
                       ,
      "        (Float mant:exp: (mant * (x-prime mant)) (exp + (x-prime exp))))"
                       ,
                     ";      We compute the reciprocal using the algebraic law "
                       , ";                                                   "
                       ,
                      ";       frac1m \\atimes10^e = frac10^9m \\atimes10^9 \\ "
                       , ";       atimes10^e = frac10^9m \\atimes10^-e-9 .     "
                       , ";                                                   "
                       ,
                     ";      Dividing 10^9 by m ensures we don't lose too much "
                       , ";      precision from m.                            "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method reciprocal ()"
                       ,
                  "        (Float mant:exp: (1000000000 div: mant) (-9 - exp)))"
                       ,
                        ";      Coercing converts to [[Float]], and converting "
                       , ";      [[Float]] to [[Float]] is the identity.      "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method coerce: (aNumber) (aNumber asFloat))"
                       , "    (method asFloat () self)"
                       ,
                 ";      When converting a float to another class of number, a "
                       ,
                     ";      negative exponent means divide, and a nonnegative "
                       , ";      exponent means multiply.                     "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method asInteger ()"
                       , "        ((exp isNegative) ifTrue:ifFalse:"
                       ,
                 "            {(mant div: (10 raisedToInteger: (exp negated)))}"
                       , "            {(mant    * (10 raisedToInteger: exp))}))"
                       ,
                 ";      To get a fraction, we either put a power of 10 in the "
                       ,
                       ";      denominator, or we make a product with 1 in the "
                       , ";      denominator.                                 "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method asFraction ()"
                       , "        ((exp < 0) ifTrue:ifFalse:"
                       ,
    "            {(Fraction num:den: mant (10 raisedToInteger: (exp negated)))}"
                       ,
      "            {(Fraction num:den: (mant * (10 raisedToInteger: exp)) 1)}))"
                       ,
                 ";      Unlike the sign tests in [[Fraction]], the sign tests "
                       ,
                   ";      in [[Float]] aren't just an optimization: the [[<]] "
                       ,
                 ";      method sends [[negative]] to a floating-point number, "
                       ,
                     ";      so the superclass implementation of [[negative]], "
                       ,
                    ";      which sends [[</]] to self, would lead to infinite "
                       ,
                  ";      recursion. Fortunately, the sign of a floating-point "
                       ,
                      ";      number is the sign of its mantissa, so all three "
                       , ";      methods can be delegated to [[Integer]].     "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method isNegative         () (mant isNegative))"
                       ,
                       "    (method isNonnegative      () (mant isNonnegative))"
                       ,
                  "    (method isStrictlyPositive () (mant isStrictlyPositive))"
                       ,
                 ";      A floating-point number is printed as m[[x10^]]e. But "
                       , ";      we want to avoid printing a number like 77 as "
                       ,
                  ";      [[770x10^-1]]. \\stdbreak So if the [[print]] method "
                       ,
                 ";      sees a number with a negative exponent and a mantissa "
                       , ";      that is a multiple of 10, \\stdbreak          "
                       , ";                                                   "
                       ,
                       ";      it divides the mantissa by 10 and increases the "
                       ,
                  ";      exponent, continuing until the exponent reaches zero "
                       ,
                    ";      or the mantissa is no \\stdbreak longer a multiple "
                       ,
                 ";      of 10. As a result, a whole number always prints as a "
                       ,
                  ";      whole number times 10^0, no matter what its internal "
                       , ";      representation is.                           "
                       , ";      <other methods of class [[Float]]>=          "
                       , "    (method print () "
                       , "        (self print-normalize) "
                       , "        (mant print) ('x10^ print) (exp print)"
                       , "        (self normalize))"
                       , ""
                       , "    (method print-normalize ()"
                       ,
                 "        ({((exp < 0) and: {((mant mod: 10) = 0)})} whileTrue:"
                       ,
                 "            {(set exp (exp + 1)) (set mant (mant div: 10))}))"
                       , ")"
                       , ";  Implementation of Unicode characters         "
                       , ";                                               "
                       ,
                     ";  As in the other bridge languages, a Unicode character "
                       ,
                       ";  prints using the UTF-8 encoding. The [[Char]] class "
                       ,
                     ";  defines a representation, initialization methods, and "
                       , ";  a [[print]] method. It must also redefine [[=]], "
                       ,
                       ";  because two objects that represent the same Unicode "
                       ,
                        ";  character should be considered equal, even if they "
                       ,
                     ";  are not the same object. The representation invariant "
                       ,
                        ";  is that [[code-point]] is an integer between 0 and "
                       , ";  hexadecimal 1fffff.                          "
                       ,
     ";  <predefined uSmalltalk classes and values that use numeric literals>= "
                       , "(class Char"
                       , "   [subclass-of Object]"
                       , "   [ivars code-point]"
                       , "   (class-method new: (n) ((self new) init: n))"
                       ,
                 "   (method init:      (n) (set code-point n) self) ;; private"
                       ,
                      "   (method print      ()  (primitive printu code-point))"
                       ,
                      "   (method =          (c) (code-point = (c code-point)))"
                       , "   (method code-point ()  code-point) ;; private"
                       , ")"
                       , ";  The predefined characters are defined using their "
                       ,
                       ";  code points, which coincide with 7-bit ASCII codes. "
                       ,
     ";  <predefined uSmalltalk classes and values that use numeric literals>= "
                       ,
        "(val newline      (Char new: 10))   (val left-round   (Char new:  40))"
                       ,
        "(val space        (Char new: 32))   (val right-round  (Char new:  41))"
                       ,
        "(val semicolon    (Char new: 59))   (val left-curly   (Char new: 123))"
                       ,
        "(val quote        (Char new: 39))   (val right-curly  (Char new: 125))"
                       ,
        "                                    (val left-square  (Char new:  91))"
                       ,
        "                                    (val right-square (Char new:  93))"
                       ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                       , ";  {protocol}[[Collection]] \\pmspecies --- Answer a "
                       ,
                      ";  class that should be used to create new instances of "
                       , ";  collections like the receiver, to help with the "
                       , ";  implementation of [[select:]], [[collect:]], and "
                       , ";  similar methods.                             "
                       ,
                    ";  \\mprintName --- Print the name of the object's class, "
                       ,
                     ";  to help with the implementation of [[print]]. (Almost "
                       ,
                       ";  all [[Collection]] objects print as the name of the "
                       , ";  class, followed by the list of elements in   "
                       ,
                       ";  parentheses. [[Array]] objects omit the name of the "
                       , ";  class.)                                      "
                       ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                       , ";  {protocol}                                   "
                       , ";                                               "
                       ,
                      ";  Private methods internal to [[Collection]] classes.  "
                       , ";  [*]                                          "
                       ,
";  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ "
                       , ";                                               "
                       , ";  Reuse via inheritance: class Collection      "
                       , ";                                               "
                       , ";  [*] Smalltalk collections enjoy the rich protocol "
                       , ";  summarized in \\crefpagesmall.proto.Collection. "
                       ,
                       ";  The protocol is a joy to work with; it includes not "
                       , ";  only object-oriented analogs to functions like "
                       , ";  [[map]], [[filter]], and [[foldl]], but also many "
                       ,
                        ";  other methods, including methods that add, remove, "
                       ,
                       ";  find, and count elements. And the protocol supports "
                       , ";  not only lists but also several other forms of "
                       , ";  collection. All of this functionality is provided "
                       ,
                        ";  using just four subclass responsibilities: you can "
                       , ";  add a new collection to the hierarchy by defining "
                       ,
                       ";  [[do:]], [[add:]], [[remove:ifAbsent:]], and [[=]]. "
                       , ";  <collection classes>=                        "
                       , "(class Collection"
                       , "  [subclass-of Object] ; abstract"
                       ,
               "  (method do:     (aBlock)       (self subclassResponsibility))"
                       ,
               "  (method add:    (newObject)    (self subclassResponsibility))"
                       , "  (method remove:ifAbsent: (oldObject exnBlock)"
                       ,
               "                                 (self subclassResponsibility))"
                       ,
               "  (method =       (aCollection)  (self subclassResponsibility))"
                       ,
                   ";    To create a singleton collection, we send [[add:]] to "
                       , ";    a new instance:                              "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (class-method with: (anObject)"
                       , "      ((self new) add: anObject))"
                       , ";    To create a collection that contains all of an "
                       ,
                       ";    argument's elements, we send [[addAll:]] to a new "
                       , ";    instance:                                    "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (class-method withAll: (aCollection)"
                       , "      ((self new) addAll: aCollection))"
                       ,
                   ";    Given [[add:]], [[remove:ifAbsent:]], and [[do:]], we "
                       ,
                      ";    can easily implement [[remove:]], [[addAll:]], and "
                       ,
                   ";    [[removeAll:]]. When any of these messages is sent to "
                       ,
                      ";    an object of a subclass, the message dispatches to "
                       ,
                     ";    one of the methods defined here. When these methods "
                       , ";    in turn send the messages [[do:]],           "
                       ,
                    ";    [[remove:ifAbsent:]], and [[add:]], they dispatch to "
                       ,
                   ";    the implementations of [[do:]], [[remove:ifAbsent:]], "
                       , ";    and [[add:]], that are defined in the subclass. "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (method remove: (oldObject) "
                       ,
"      (self remove:ifAbsent: oldObject {(self error: 'tried-to-remove-absent-object)}))"
                       , "  (method addAll: (aCollection) "
                       , "      (aCollection do: [block (x) (self add: x)])"
                       , "      self)"
                       , "  (method removeAll: (aCollection) "
                       , "      (aCollection do: [block (x) (self remove: x)])"
                       , "      self)"
                       ,
                       ";    In addition to these mutators, the [[Collection]] "
                       ,
                      ";    protocol in \\crefsmall.proto.Collection defines a "
                       , ";    host of observers, including [[isEmpty]] and "
                       ,
                     ";    [[size]], among others. The default implementations "
                       , ";    given here iterate through the elements of the "
                       ,
                     ";    collection using [[do:]]. \\stdbreak Using a linear "
                       ,
                       ";    search to compute [[size]], for example, may seem "
                       ,
                    ";    terribly inefficient, but if a subclass knows a more "
                       ,
                       ";    efficient way to compute the number of \\stdbreak "
                       ,
                       ";    elements, it should redefine the [[size]] method. "
                       ,
                   ";    And for some collections, like [[List]], there really "
                       ,
                   ";    is no better way to compute size or count occurrences "
                       , ";    than to visit all the elements.              "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (method size () [locals temp]"
                       , "      (set temp 0)"
                       , "      (self do: [block (_) (set temp (temp + 1))])"
                       , "      temp)"
                       , "  (method occurrencesOf: (anObject) [locals temp]"
                       , "      (set temp 0)"
                       , "      (self do: [block (x)"
                       ,
                   "         ((x = anObject) ifTrue: {(set temp (temp + 1))})])"
                       , "      temp)"
                       , ";    Other observers also start by iterating using "
                       , ";    [[do:]], but they can cut an iteration short by "
                       , ";    evaluating a [[return]] expression. Like the "
                       ,
                     ";    implementations of [[size]] and [[occurrencesOf:]], "
                       ,
                   ";    these implementations are as efficient as is possible "
                       , ";    with a linked list. [*]                      "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (method isEmpty () "
                       , "      (self do: [block (_) (return false)])"
                       , "      true)"
                       , "  (method includes: (anObject)"
                       ,
         "      (self do: [block (x) ((x = anObject) ifTrue: {(return true)})])"
                       , "      false)"
                       , "  (method detect:ifNone: (aBlock exnBlock)"
                       ,
         "      (self do: [block (x) ((aBlock value: x) ifTrue: {(return x)})])"
                       , "      (exnBlock value))"
                       , "  (method detect: (aBlock)"
                       ,
       "      (self detect:ifNone: aBlock {(self error: 'no-object-detected)}))"
                       , ";    In addition to mutators and observers, the   "
                       ,
                        ";    [[Collection]] protocol also provides iterators. "
                       , ";    These iterators have something in common with "
                       ,
                     ";    micro-Scheme's higher-order functions on lists. For "
                       ,
                      ";    example, [[do:]] resembles micro-Scheme's [[app]], "
                       , ";    and [[inject:into:]] resembles micro-Scheme's "
                       , ";    [[foldl]]. And here is another case where data "
                       ,
                      ";    abstraction using objects offers an advantage over "
                       ,
                   ";    abstract data types: unlike micro-Scheme's [[foldl]], "
                       ,
                   ";    [[inject:into:]] works on any collection, not just on "
                       , ";    lists.                                       "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (method inject:into: (thisValue binaryBlock)"
                       ,
"     (self do: [block (x) (set thisValue (binaryBlock value:value: x thisValue))])"
                       , "     thisValue)"
                       ,
                   ";    The methods [[select:]], [[reject:]] and [[collect:]] "
                       , ";    resemble micro-Scheme's [[filter]] and [[map]] "
                       ,
                  ";    functions. \\stdbreak Like [[inject:into:]], they work "
                       , ";    on all collections, not just on lists.       "
                       , ";    The implementations use [[species]], which is a "
                       ,
                       ";    private message used to create ``a new collection "
                       , ";    like the receiver.''                         "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (method select: (aBlock) [locals temp]"
                       , "     (set temp ((self species) new))"
                       ,
       "     (self do: [block (x) ((aBlock value: x) ifTrue: {(temp add: x)})])"
                       , "     temp)"
                       , "  (method reject: (aBlock)"
                       ,
                      "     (self select: [block (x) ((aBlock value: x) not)]))"
                       , "  (method collect: (aBlock) [locals temp]"
                       , "     (set temp ((self species) new))"
                       ,
                     "     (self do: [block (x) (temp add: (aBlock value: x))])"
                       , "     temp)"
                       ,
                    ";    A [[species]] defaults to the class of the receiver. "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (method species () (self class))"
                       ,
                       ";    Finally, [[Collection]] defines its own [[print]] "
                       ,
                     ";    method. By default, a collection prints as the name "
                       ,
                   ";    of its class, followed by a parenthesized list of its "
                       , ";    elements.                                    "
                       , ";    <other methods of class [[Collection]]>=     "
                       , "  (method print ()"
                       , "      (self printName)"
                       , "      (left-round print)"
                       , "      (self do: [block (x) (space print) (x print)])"
                       , "      (space print)"
                       , "      (right-round print)"
                       , "      self)"
                       , "  (method printName () (((self class) name) print))"
                       , ")"
                       , ";  Implementation of [[KeyedCollection]]        "
                       , ";                                               "
                       , ";  A keyed collection provides access to key-value "
                       , ";  pairs. Any subclass must define methods      "
                       , ";  [[associationsDo:]], which replaces [[do:]], "
                       ,
                       ";  [[at:put:]], which sometimes replaces [[add:]], and "
                       , ";  [[removeKey:ifAbsent:]], which replaces      "
                       ,
                      ";  [[remove:ifAbsent:]]. The key-value pairs answer the "
                       , ";  [[Association]] protocol.                    "
                       , ";  <collection classes>=                        "
                       , "(class KeyedCollection"
                       , "    [subclass-of Collection]  ; abstract class"
                       ,
 "    (method at:put: (key value)                (self subclassResponsibility))"
                       ,
 "    (method associationsDo: (aBlock)           (self subclassResponsibility))"
                       ,
 "    (method removeKey:ifAbsent: (key exnBlock) (self subclassResponsibility))"
                       ,
                  ";      Given [[associationsDo:]], we implement the required "
                       ,
                        ";      [[do:]] method by iterating over associations. "
                       , ";      <other methods of class [[KeyedCollection]]>= "
                       , "    (method do: (aBlock) "
                       ,
"        (self associationsDo: [block (anAssoc) (aBlock value: (anAssoc value))]))"
                       , ";      <other methods of class [[KeyedCollection]]>= "
                       , "    (method at: (key)    "
                       ,
               "        (self at:ifAbsent: key {(self error: 'key-not-found)}))"
                       , "    (method at:ifAbsent: (key exnBlock) "
                       ,
"        ((self associationAt:ifAbsent: key {(return (exnBlock value))}) value))"
                       , "    (method includesKey: (key) "
                       ,
                       "        ((self associationAt:ifAbsent: key {}) notNil))"
                       , "    (method associationAt: (key) "
                       ,
    "        (self associationAt:ifAbsent: key {(self error: 'key-not-found)}))"
                       , "    (method associationAt:ifAbsent: (key exnBlock)"
                       ,
"        (self associationsDo: [block (x) (((x key) = key) ifTrue: {(return x)})])"
                       , "        (exnBlock value))"
                       , ";      When a key is found, method                  "
                       ,
                     ";      [[associationAt:ifAbsent:]] terminates the search "
                       ,
                    ";      immediately by evaluating a [[return]] expression. "
                       ,
                   ";      All the other methods benefit from this efficiency. "
                       , ";      I use the same technique for finding keys.   "
                       , ";      <other methods of class [[KeyedCollection]]>= "
                       , "    (method keyAtValue: (value) "
                       ,
   "        (self keyAtValue:ifAbsent: value {(self error: 'value-not-found)}))"
                       , "    (method keyAtValue:ifAbsent: (value exnBlock)"
                       , "        (self associationsDo: [block (x) "
                       ,
                "            (((x value) = value) ifTrue: {(return (x key))})])"
                       , "        (exnBlock value))"
                       , ";      To remove a key, use [[removeAt:ifAbsent]].  "
                       , ";      <other methods of class [[KeyedCollection]]>= "
                       , "    (method removeKey: (key)    "
                       ,
        "        (self removeKey:ifAbsent: key {(self error: 'key-not-found)}))"
                       ,
                    ";      Rather than have to implement [[=]] separately for "
                       ,
                   ";      dictionaries, lists, and arrays, I can implement it "
                       ,
                      ";      once, here, for all keyed collections. Two keyed "
                       ,
                    ";      collections are equivalent if they have equivalent "
                       ,
                     ";      associations. For efficiency, I look first for an "
                       ,
                     ";      association that's in the receiver but not in the "
                       ,
                      ";      argument. If I find one, the collections are not "
                       ,
                       ";      equivalent, and I return [[false]] immediately. "
                       ,
                  ";      Otherwise, I just have to confirm that both receiver "
                       , ";      and argument have the same number of         "
                       , ";      associations---if so, they are equivalent.   "
                       , ";      <other methods of class [[KeyedCollection]]>= "
                       , "    (method = (collection)"
                       , "        (self associationsDo:"
                       , "            [block (assn)"
                       , "                 (((assn value) = "
                       ,
"                              (collection at:ifAbsent: (assn key) {(return false)})) ifFalse:"
                       , "                           {(return false)})])"
                       , "        ((self size) = (collection size)))"
                       , ")"
                       , ";  Implementation of [[SequenceableCollection]] "
                       , ";                                               "
                       ,
                     ";  The abstract class [[SequenceableCollection]] defines "
                       ,
                       ";  methods used by [[KeyedCollection]]s whose keys are "
                       , ";  consecutive integers. \\stdbreak Because keys are "
                       , ";  consecutive integers, we can implement       "
                       , ";  [[at:ifAbsent:]] by tracking the value of the key "
                       , ";  inside a [[do:]] loop, without ever having to "
                       , ";  allocate an [[Association]]. \\stdbreak       "
                       , ";  This implementation is more efficient than the "
                       , ";  generic implementation inherited from class  "
                       ,
                      ";  [[KeyedCollection]]. Method [[associationsDo:]] also "
                       , ";  loops over consecutive keys.                 "
                       , ";  <collection classes>=                        "
                       , "(class SequenceableCollection"
                       , "    [subclass-of KeyedCollection] ; abstract class"
                       ,
                        "    (method firstKey () (self subclassResponsibility))"
                       ,
                        "    (method lastKey  () (self subclassResponsibility))"
                       , "    (method last     () (self at: (self  lastKey)))"
                       , "    (method first    () (self at: (self firstKey)))"
                       ,
                    "    (method at:ifAbsent: (index exnBlock) [locals current]"
                       , "        (set current (self firstKey))"
                       , "        (self do: [block (v)"
                       , "            ((current = index) ifTrue: {(return v)})"
                       , "            (set current (current + 1))])"
                       , "        (exnBlock value))"
                       ,
                       "    (method associationsDo: (bodyBlock) [locals i last]"
                       , "        (set i    (self firstKey))"
                       , "        (set last (self lastKey))"
                       , "        ({(i <= last)} whileTrue:"
                       ,
   "            {(bodyBlock value: (Association withKey:value: i (self at: i)))"
                       , "             (set i (i + 1))}))"
                       , ")"
                       ,
                      ";  The representation of a [[List]] stores a pointer to "
                       , ";  the sentinel in instance variable [[sentinel]]. "
                       , ";  <collection classes>=                        "
                       , ";  The hard work of implementing the list methods is "
                       ,
                      ";  done by methods defined on cons cells. We begin with "
                       ,
                      ";  the simple methods that expose the representation as "
                       ,
                      ";  a pair of car and cdr. The [[pred:]] method makes it "
                       ,
                       ";  possible to tell any cons cell what its predecessor "
                       , ";  is, but unless the cons cell is a sentinel, the "
                       ,
                     ";  information is thrown away. (The sentinel an instance "
                       , ";  of a subclass of [[Cons]].)                  "
                       , ";  <classes that define cons cells and sentinels>= "
                       , "(class Cons"
                       , "    [subclass-of Object]"
                       , "    [ivars car cdr]"
                       , "    (method car ()           car)"
                       , "    (method cdr ()           cdr)"
                       , "    (method car: (anObject)  (set car anObject) self)"
                       , "    (method cdr: (anObject)  (set cdr anObject) self)"
                       , "    (method pred: (aCons)    nil)"
                       ,
                       ";      Insertion and deletion use the standard pointer "
                       ,
                  ";      manipulations for a circularly linked list. The only "
                       ,
                  ";      unusual bit is that when we delete or insert a node, "
                       ,
                  ";      we notify the successor node of its new predecessor. "
                       , ";      <more methods of class [[Cons]]>=            "
                       , "    (method deleteAfter () [locals answer]"
                       , "        (set answer (cdr car))"
                       , "        (set cdr    (cdr cdr))"
                       , "        (cdr pred: self)"
                       , "        answer)"
                       , "    (method insertAfter: (anObject)"
                       ,
                       "        (set cdr (((Cons new) cdr: cdr) car: anObject))"
                       , "        ((cdr cdr) pred: cdr)"
                       , "        anObject)"
                       ,
                   ";      To iterate over all the cons cells in a list, we do "
                       ,
                 ";      the current cons cell, then continue with a tail call "
                       ,
                      ";      to the [[do:]] method of the next cons cell. The "
                       ,
                   ";      iteration terminates in the sentinel, whose [[do:]] "
                       , ";      method does nothing.                         "
                       , ";      <more methods of class [[Cons]]>=            "
                       , "    (method do: (aBlock)"
                       , "        (aBlock value: car)"
                       , "        (cdr do: aBlock))"
                       ,
                   ";      Similarly, to remove the first cons cell satisfying "
                       ,
                   ";      [[aBlock]], we try the current cons cell, and if it "
                       ,
                     ";      works, we remove it using [[(pred deleteAfter)]]. "
                       ,
                  ";      Otherwise, we continue by trying the next cons cell. "
                       ,
                      ";      If we get to the sentinel, we haven't found what "
                       ,
                       ";      we're looking for, and we terminate the loop by "
                       ,
                 ";      sending the [[value]] message to the exception block. "
                       , ";      <more methods of class [[Cons]]>=            "
                       ,
               "    (method rejectOne:ifAbsent:withPred: (aBlock exnBlock pred)"
                       , "        ((aBlock value: self) ifTrue:ifFalse:"
                       , "            {(pred deleteAfter)}"
                       ,
       "            {(cdr rejectOne:ifAbsent:withPred: aBlock exnBlock self)}))"
                       , ")"
                       , ";  The remaining instance methods of class      "
                       , ";  [[ListSentinel]] expose the [[pred]] pointer. The "
                       ,
                      ";  class method [[new]] allocates a new sentinel, whose "
                       , ";  [[pred]] and [[cdr]] both point to itself. Such a "
                       , ";  sentinel represents an empty list.           "
                       , ";  <classes that define cons cells and sentinels>= "
                       , "(class ListSentinel"
                       , "    [subclass-of Cons]"
                       , "    [ivars pred]"
                       , "    (method pred: (aCons)   (set pred aCons))"
                       , "    (method pred  ()        pred)"
                       , "    (class-method new ()    "
                       , "        [locals tmp]"
                       , "        (set tmp (super new))"
                       , "        (tmp pred: tmp)"
                       , "        (tmp  cdr: tmp)"
                       , "        tmp)"
                       ,
                        ";      <iterating methods of class [[ListSentinel]]>= "
                       , "    (method do: (aBlock) nil)"
                       ,
                        ";      <iterating methods of class [[ListSentinel]]>= "
                       ,
               "    (method rejectOne:ifAbsent:withPred: (aBlock exnBlock pred)"
                       , "        (exnBlock value)))"
                       , "(class List"
                       , "    [subclass-of SequenceableCollection]"
                       , "    [ivars sentinel]"
                       ,
   "    (class-method new ()        ((super new) sentinel: (ListSentinel new)))"
                       ,
              "    (method sentinel: (s)       (set sentinel s) self) ; private"
                       ,
                 "    (method isEmpty   ()        (sentinel == (sentinel cdr)))"
                       ,
                        "    (method last      ()        ((sentinel pred) car))"
                       ,
                  "    (method do:       (aBlock)  ((sentinel cdr) do: aBlock))"
                       ,
                   ";      The method [[addLast:]] mutates a list by adding an "
                       ,
                   ";      element to the end. This means inserting an element "
                       , ";      just after the predecessor of the sentinel.  "
                       ,
                       ";      Similarly, [[addFirst:]] inserts just after the "
                       ,
                  ";      sentinel itself. Having a sentinel means there is no "
                       , ";      special-case code for an empty list.         "
                       , ";      <other methods of class [[List]]>=           "
                       ,
      "    (method addLast:  (item)   ((sentinel pred) insertAfter: item) self)"
                       ,
      "    (method addFirst: (item)   (sentinel insertAfter: item)        self)"
                       , "    (method add:      (item)   (self addLast: item))"
                       ,
                  ";      To remove the first element of a list, we remove the "
                       ,
                 ";      element after the sentinel. Removing the last element "
                       , ";      is left as Exercise [->].                    "
                       , ";      <other methods of class [[List]]>=           "
                       ,
                        "    (method removeFirst ()     (sentinel deleteAfter))"
                       , "    (method removeLast  ()     (self leftAsExercise))"
                       ,
                   ";      To remove a particular element, we delegate the job "
                       , ";      to the first cons cell in the list.          "
                       , ";      <other methods of class [[List]]>=           "
                       , "    (method remove:ifAbsent: (oldObject exnBlock)"
                       , "        ((sentinel cdr)"
                       , "            rejectOne:ifAbsent:withPred:"
                       , "            [block (x) (oldObject = (x car))]"
                       , "            exnBlock"
                       , "            sentinel))"
                       , ";      Removal by key is also left as an exercise.  "
                       , ";      <other methods of class [[List]]>=           "
                       ,
           "    (method removeKey:ifAbsent: (n exnBlock) (self leftAsExercise))"
                       , ";      [[                                           "
                       ,
                   ";      List]] is a subclass of [[SequenceableCollection]], "
                       ,
                    ";      so it must answer messages involving integer keys. "
                       , ";      The first key in a [[List]] is always 0.     "
                       , ""
                       , ";      <other methods of class [[List]]>=           "
                       , "    (method firstKey () 0)"
                       , "    (method lastKey  () ((self size) - 1))"
                       , "    (method at:put: (n value) [locals tmp]"
                       , "        (set tmp (sentinel cdr))"
                       , "        ({(n = 0)} whileFalse:"
                       , "           {(set n (n - 1))"
                       , "            (set tmp (tmp cdr))})"
                       , "        (tmp car: value)"
                       , "        self)"
                       ,
                 ";      Method [[at:put:]] simply walks the [[car]] links n-1 "
                       ,
                    ";      times. If [[n]] is out of range, you can get wrong "
                       ,
                  ";      answers. Wrong answers can be prevented in more than "
                       ,
                  ";      one way; \\crefpagesmall.ex.List-at:put: asks you to "
                       ,
                        ";      build and compare two preventative mechanisms. "
                       , ""
                       , ")"
                       , ";  Collection things                            "
                       , ";                                               "
                       , ";  Class [[Association]]                        "
                       , ";                                               "
                       ,
                       ";  Method [[associationsDo:]] visits all the key-value "
                       , ";  pairs in a keyed collection. A key-value pair is "
                       ,
                        ";  represented by an object of class [[Association]]. "
                       , ";  <collection classes>=                        "
                       , "(class Association"
                       , "   [subclass-of Object]"
                       , "   [ivars key value]"
                       ,
         "   (class-method withKey:value: (x y) ((self new) setKey:value: x y))"
                       ,
      "   (method setKey:value: (x y) (set key x) (set value y) self) ; private"
                       , "   (method key       ()  key)"
                       , "   (method value     ()  value)"
                       , "   (method setKey:   (x) (set key   x))"
                       , "   (method setValue: (y) (set value y))"
                       ,
             "   (method =         (a) ((key = (a key)) & (value = (a value))))"
                       , ")"
                       , ";  Implementation of [[Dictionary]]             "
                       , ";                                               "
                       , ";  [*] A [[Dictionary]] is the simplest and least "
                       , ";  specialized of the keyed collections. If all "
                       ,
                      ";  uSmalltalk objects could be hashed, we would want to "
                       ,
                    ";  represent a [[Dictionary]] as a hash table. \\stdbreak "
                       ,
                        ";  Because not every uSmalltalk object can be hashed, "
                       ,
                     ";  we use a list of [[Association]]s instead. \\stdbreak "
                       ,
                       ";  The abstraction is a finite map, which is to say, a "
                       , ";  function with a finite domain. \\stdbreak     "
                       , ";  The representation is a list of [[Association]]s "
                       , ";  stored in instance variable [[table]]. \\stdbreak "
                       ,
                     ";  The representation invariant is that in [[table]], no "
                       , ";  single [[key]] appears in more than one      "
                       ,
                      ";  [[Association]]. \\stdbreak The abstraction function "
                       , ";  takes the representation to the function that is "
                       ,
                       ";  undefined on all [[key]]s not in [[table]] and that "
                       ,
                       ";  maps each [[key]] in [[table]] to the corresponding "
                       , ";  [[value]].                                   "
                       , ";  <collection classes>=                        "
                       , "(class Dictionary"
                       , "    [subclass-of KeyedCollection]"
                       , "    [ivars table] ; list of Associations"
                       ,
                   "    (class-method new ()      ((super new) initDictionary))"
                       ,
          "    (method initDictionary () (set table (List new)) self) ; private"
                       ,
                 ";      The operations that [[Dictionary]] must implement are "
                       , ";      [[associationsDo:]], [[at:put]], and         "
                       ,
                   ";      [[removeKey:ifAbsent]]. Iteration over associations "
                       ,
                      ";      can be delegated to the list of associations. To "
                       ,
                  ";      implement [[at:put:]], we search for the association "
                       , ";      containing the given key. If we find such an "
                       ,
                  ";      association, we mutate its value. If we find no such "
                       , ";      association, we add one.                     "
                       , ";      <other methods of class [[Dictionary]]>=     "
                       ,
                      "    (method associationsDo: (aBlock) (table do: aBlock))"
                       , "    (method at:put: (key value) [locals tempassoc]"
                       ,
                 "        (set tempassoc (self associationAt:ifAbsent: key {}))"
                       , "        ((tempassoc isNil) ifTrue:ifFalse:"
                       ,
            "             {(table add: (Association withKey:value: key value))}"
                       , "             {(tempassoc setValue: value)})"
                       , "        self)"
                       ,
                        ";      Removing a key requires that we first save the "
                       ,
                        ";      removed value, so we can answer it. The actual "
                       ,
                 ";      removal is done by sending the [[reject:]] message to "
                       , ";      the representation.                          "
                       , ";      <other methods of class [[Dictionary]]>=     "
                       , "    (method removeKey:ifAbsent: (key exnBlock)"
                       ,
                     "       [locals value-removed] ; value found if not absent"
                       ,
"       (set value-removed (self at:ifAbsent: key {(return (exnBlock value))}))"
                       ,
"       (set table (table reject: [block (assn) (key = (assn key))])) ; remove assoc"
                       , "       value-removed)"
                       ,
                 ";      Because more than one association might have the same "
                       , ";      value, it makes no sense to implement        "
                       , ";      [[remove:ifAbsent:]].                        "
                       , ";      <other methods of class [[Dictionary]]>=     "
                       , "    (method remove:ifAbsent: (value exnBlock)"
                       ,
                "       (self error: 'Dictionary-uses-remove:key:-not-remove:))"
                       ,
                    ";      And because a dictionary requires not just a value "
                       ,
                  ";      but also a key, the only sensible thing to add is an "
                       , ";      [[Association]].                             "
                       , ";      <other methods of class [[Dictionary]]>=     "
                       , "    (method add: (anAssociation)"
                       ,
               "      (self at:put: (anAssociation key) (anAssociation value)))"
                       , ";      A dictionary's [[print]] method uses         "
                       , ";      [[associationsDo:]].                         "
                       , ";      <other methods of class [[Dictionary]]>=     "
                       , "    (method print () [locals print-comma]"
                       , "        (set print-comma false)"
                       , "        (self printName)"
                       , "        (left-round print)"
                       , "        (self associationsDo:"
                       , "            [block (x) (space print)"
                       ,
       "                       (print-comma ifTrue: {(', print) (space print)})"
                       , "                       (set print-comma true)"
                       ,
                        "                       ((x key) print)   (space print)"
                       ,
                        "                       ('|--> print)     (space print)"
                       , "                       ((x value) print)])"
                       , "        (space print)"
                       , "        (right-round print)"
                       , "        self)"
                       , ")"
                       ,
                      ";  Many of [[Array]]'s methods are primitive, including "
                       , ";  array creation and the [[at:]], [[at:put:]], and "
                       ,
                        ";  [[size]] methods. These methods are defined in the "
                       , ";  interpreter, in chunks [->]-- [->] in \\secref "
                       , ";  small.array-primops.section. [*]             "
                       , ";  <collection classes>=                        "
                       , "(class Array"
                       ,
        "    [subclass-of SequenceableCollection] ; representation is primitive"
                       ,
                 "    (class-method new: (size) (primitive arrayNew self size))"
                       ,
 "    (class-method new  ()     (self error: 'size-of-Array-must-be-specified))"
                       ,
                     "    (method size       ()     (primitive arraySize self))"
                       ,
              "    (method at:        (key)       (primitive arrayAt self key))"
                       ,
"    (method at:put:    (key value) (primitive arrayUpdate self key value) self)"
                       ,
               "    (method printName  () nil) ; names of arrays aren't printed"
                       , ";      Compromising on protocol: class [[Array]]    "
                       , ";                                                   "
                       , ";      [*] Like a list, an array is a sequenceable  "
                       ,
                        ";      collection, but with different cost tradeoffs: "
                       ,
                    ";      methods [[at:]] and [[at:put:]] take only constant "
                       ,
                 ";      time, but after it is allocated, an array cannot grow "
                       ,
                     ";      or shrink. As a result, subclass responsibilities "
                       , ";      [[add:]], [[remove:ifAbsent]], and           "
                       ,
                  ";      [[removeKey:ifAbsent]] are not actually implemented; "
                       ,
                    ";      sending any of those messages results in a checked "
                       , ";      run-time error.                              "
                       , ";      <other methods of class [[Array]]>=          "
                       ,
                  "    (method add:                (x)   (self fixedSizeError))"
                       ,
                  "    (method remove:ifAbsent:    (x b) (self fixedSizeError))"
                       ,
                  "    (method removeKey:ifAbsent: (x b) (self fixedSizeError))"
                       ,
  "    (method fixedSizeError      ()    (self error: 'arrays-have-fixed-size))"
                       ,
                 ";      The implementations of [[firstKey]], [[lastKey]], and "
                       , ";      [[do:]] rely on the primitives:              "
                       , ";      <other methods of class [[Array]]>=          "
                       , "    (method firstKey () 0)"
                       , "    (method lastKey  () ((self size) - 1))"
                       , "    (method do: (aBlock) [locals index]"
                       , "        (set index (self firstKey))"
                       , "        ((self size) timesRepeat:"
                       , "           {(aBlock value: (self at: index))"
                       , "            (set index (index + 1))}))"
                       ,
                      ";      An array is mutable, but it has a fixed size, so "
                       ,
                      ";      trying to add or remove an element is senseless. "
                       , ";      Because [[add:]] doesn't work, the inherited "
                       ,
                 ";      implementations of [[select:]] and [[collect:]] don't "
                       ,
                  ";      work either. Writing implementations that do work is "
                       , ";      \\crefpagesmall.ex.array-select.              "
                       ,
                     ";      <other methods of class [[Array]] ((prototype))>= "
                       ,
    "    (method select:  (_) (self error: 'select-on-arrays-left-as-exercise))"
                       ,
   "    (method collect: (_) (self error: 'collect-on-arrays-left-as-exercise))"
                       , ")"
                       , ";  The abstraction, representation, abstraction "
                       , ";  function, and invariant are as they would be in a "
                       ,
                     ";  language with abstract data types. \\stdbreak But the "
                       ,
                     ";  operations that need to be implemented are different. "
                       ,
                       ";  It is true that a [[Set]] object needs to implement "
                       ,
                       ";  everything in its interface, which means the entire "
                       ,
                     ";  [[Collection]] protocol. \\stdbreak But it doesn't do "
                       ,
                        ";  all the work itself: almost all of the protocol is "
                       ,
                       ";  implemented in class [[Collection]], \\stdbreak and "
                       , ";  [[Set]] inherits those implementations. The only "
                       ,
                       ";  methods that must be implemented in [[Set]] are the "
                       , ";  ``subclass responsibility'' methods [[do:]], "
                       , ";  [[add:]], [[remove:ifAbsent:]], [[=]], and   "
                       ,
                       ";  [[species]], plus the private method [[printName]]. "
                       , ";  <collection classes>=                        "
                       , "(class Set"
                       , "    [subclass-of Collection]"
                       ,
               "    [ivars members]  ; list of elements [invariant: no repeats]"
                       , "    (class-method new () ((super new) initSet))"
                       ,
             "    (method initSet   () (set members (List new)) self) ; private"
                       , "    (method do: (aBlock) (members do: aBlock))"
                       , "    (method add: (item)"
                       ,
             "        ((members includes: item) ifFalse: {(members add: item)})"
                       , "        self)"
                       , "    (method remove:ifAbsent: (item exnBlock) "
                       , "        (members remove:ifAbsent: item exnBlock)"
                       , "        self)"
                       , "    (method =  (s) [locals looks-similar]"
                       , "       (set looks-similar ((self size) = (s size)))"
                       , "       (looks-similar ifTrue:"
                       ,
                    "           {(self do: [block (x) ((s includes: x) ifFalse:"
                       ,
   "                                           {(set looks-similar false)})])})"
                       , "       looks-similar)"
                       , ")"
                        ])
      fun errmsg s = eprintlnTrace ("error in predefined class: " ^ s)
  in  readEvalPrintWith errmsg (xdefs, initialXi, noninteractive)
      before (if logging then print "\nops.predefined_ends ()\n" else ())
  end
(* Before we can close the cycles, we have to create *)
(* [[VAL]] bindings for [[true]] and [[false]]. Because *)
(* the parser prevents user code from binding [[true]] *)
(* and [[false]], we can't do this in uSmalltalk; the *)
(* [[val]] bindings are written in ML.          *)
(* <implementations of \usmalltalk\ primitives and definition of [[initialBasis]]>= *)
local 
  fun newInstance classname = SEND (nullsrc, VAR classname, "new", [])
in
  val initialXi = processPredefined (VAL ("true",  newInstance "True" ),
                                                                      initialXi)
  val initialXi = processPredefined (VAL ("false", newInstance "False"),
                                                                      initialXi)
end
(* Once we've read the class definitions, we can close *)
(* the cycles, update the ref cells, and we're almost *)
(* ready to go. By this time, all the necessary classes *)
(* should be defined, so if any cycle fails to close, we *)
(* halt the interpreter with a fatal error. [*] *)
(* <implementations of \usmalltalk\ primitives and definition of [[initialBasis]]>= *)
val _ =
  ( saveLiteralClasses      initialXi
  ; saveTrueAndFalse        initialXi
  ; saveBlockClass          initialXi
  ; saveCompiledMethodClass initialXi
  ) handle NotFound n =>
      ( app eprint ["Fatal error: ", n, " is not predefined\n"]
      ; raise InternalError "this can't happen"
      )
  | e => ( eprintln "Error binding predefined classes into interpreter"; raise e
                                                                               )
(* The last step of initialization is to bind the *)
(* predefined value [[nil]]. Like bindings for [[true]] *)
(* and [[false]], a [[val]] binding for [[nil]] can't be *)
(* parsed, so the binding is written in ML.     *)
(* <implementations of \usmalltalk\ primitives and definition of [[initialBasis]]>= *)
val initialXi = processPredefined (VAL ("nil", VALUE nilValue), initialXi)
val initialBasis = initialXi


(*****************************************************************)
(*                                                               *)
(*   FUNCTION [[RUNAS]] FOR \USMALLTALK, WHICH PRINTS STACK TRACES *)
(*                                                               *)
(*****************************************************************)

(* <function [[runAs]] for \usmalltalk, which prints stack traces>= *)
fun runAs interactivity = 
  let val _ = setup_error_format interactivity
      val prompts = if prompts interactivity then stdPrompts else noPrompts
      val xdefs = filexdefs ("standard input", TextIO.stdIn, prompts)
  in  ignore (readEvalPrintWith eprintlnTrace (xdefs, initialBasis,
                                                                 interactivity))
  end 
(* To trace method calls, uSmalltalk uses a custom *)
(* [[runAs]] function; instead of [[eprintln]], it calls *)
(* [[eprintlnTrace]]. [*]                       *)
(* <boxed values 78>=                           *)
val _ = op runAs : interactivity -> unit
fun dump_global_names () = app (println o fst) initialBasis  (*OMIT*)


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


(*****************************************************************)
(*                                                               *)
(*   TYPE ASSERTIONS FOR \USMALLTALK                             *)
(*                                                               *)
(*****************************************************************)

(* Utilities for manipulating classes (from the *)
(* Supplement) [*]                              *)
(* <type assertions for \usmalltalk ((elided))>= *)
(* ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ *)
(* <boxed values 7>=                            *)
val _ = mkClass     : name -> metaclass -> class -> name list -> method list ->
                                                                           class
val _ = methodDefns : class * class -> method_def list -> method list * method
                                                                            list
val _ = findClass   : name * value ref env -> class * class
val _ = setMeta     : class * class -> unit
val _ = className   : class -> name
val _ = classId     : class -> metaclass ref
val _ = methodName  : method -> name
val _ = methodsEnv  : method list -> method env
(* <type assertions for \usmalltalk ((elided))>= *)
(* Blocks                                       *)
(*                                              *)
(* When [[eval]] interprets a [[block]] expression, *)
(* it has to give it class [[Block]], which also is not *)
(* defined until its definition is read. Therefore, the *)
(* same drill applies to blocks as applies to literal *)
(* expressions. \Crefusma.chap defines these functions: *)
(* <boxed values 13>=                           *)
val _ = mkBlock : name list * exp list * value ref env * class * frame -> value
val _ = saveBlockClass : value ref env -> unit
