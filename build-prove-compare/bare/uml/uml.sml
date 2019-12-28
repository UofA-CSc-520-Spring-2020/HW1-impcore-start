(* uml.sml S308d *)


(*****************************************************************)
(*                                                               *)
(*   EXCEPTIONS USED IN LANGUAGES WITH TYPE INFERENCE            *)
(*                                                               *)
(*****************************************************************)

(* exceptions used in languages with type inference S75c *)
exception TypeError of string
exception BugInTypeInference of string


(*****************************************************************)
(*                                                               *)
(*   \FOOTNOTESIZE SHARED: NAMES, ENVIRONMENTS, STRINGS, ERRORS, PRINTING, INTERACTION, STREAMS, \&\ INITIALIZATION *)
(*                                                               *)
(*****************************************************************)

(* \footnotesize shared: names, environments, strings, errors, printing, interaction, streams, \&\ initialization S75a *)
(* for working with curried functions: [[id]], [[fst]], [[snd]], [[pair]], [[curry]], and [[curry3]] S103c *)
fun id x = x
fun fst (x, y) = x
fun snd (x, y) = y
fun pair x y = (x, y)
fun curry  f x y   = f (x, y)
fun curry3 f x y z = f (x, y, z)
(* type declarations for consistency checking *)
val _ = op fst    : ('a * 'b) -> 'a
val _ = op snd    : ('a * 'b) -> 'b
val _ = op pair   : 'a -> 'b -> 'a * 'b
val _ = op curry  : ('a * 'b -> 'c) -> ('a -> 'b -> 'c)
val _ = op curry3 : ('a * 'b * 'c -> 'd) -> ('a -> 'b -> 'c -> 'd)
(* support for names and environments 344 *)
type name = string
(* support for names and environments 345 *)
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

(* type declarations for consistency checking *)
val _ = op emptyEnv : 'a env
val _ = op find     : name * 'a env -> 'a
val _ = op bind     : name      * 'a      * 'a env -> 'a env
val _ = op bindList : name list * 'a list * 'a env -> 'a env
(* support for names and environments S218e *)
fun duplicatename [] = NONE
  | duplicatename (x::xs) =
      if List.exists (fn x' => x' = x) xs then
        SOME x
      else
        duplicatename xs
(* type declarations for consistency checking *)
val _ = op duplicatename : name list -> name option
(* support for names and environments S302e *)
fun extend (rho, bindings) =
  foldr (fn ((x, a), rho) => bind (x, a, rho)) rho bindings
(* type declarations for consistency checking *)
val _ = op extend : 'a env * 'a env -> 'a env
(* support for names and environments S303a *)
exception DisjointUnionFailed of name
fun disjointUnion envs =
  let val env = List.concat envs
  in  case duplicatename (map fst env)
        of NONE => env
         | SOME x => raise DisjointUnionFailed x
  end
(* type declarations for consistency checking *)
val _ = op disjointUnion : 'a env list -> 'a env
(* support for detecting and signaling errors detected at run time S218d *)
exception RuntimeError of string (* error message *)
(* support for detecting and signaling errors detected at run time S218f *)
fun errorIfDups (what, xs, context) =
  case duplicatename xs
    of NONE   => ()
     | SOME x => raise RuntimeError (what ^ " " ^ x ^ " appears twice in " ^
                                                                        context)
(* type declarations for consistency checking *)
val _ = op errorIfDups : string * name list * string -> unit
(* support for detecting and signaling errors detected at run time S218g *)
exception InternalError of string (* bug in the interpreter *)
(* list functions not provided by \sml's initial basis S80b *)
fun zip3 ([], [], []) = []
  | zip3 (x::xs, y::ys, z::zs) = (x, y, z) :: zip3 (xs, ys, zs)
  | zip3 _ = raise ListPair.UnequalLengths

fun unzip3 [] = ([], [], [])
  | unzip3 (trip::trips) =
      let val (x,  y,  z)  = trip
          val (xs, ys, zs) = unzip3 trips
      in  (x::xs, y::ys, z::zs)
      end
(* list functions not provided by \sml's initial basis S80c *)
val reverse = rev
(* list functions not provided by \sml's initial basis S81a *)
fun optionList [] = SOME []
  | optionList (NONE :: _) = NONE
  | optionList (SOME x :: rest) =
      (case optionList rest
         of SOME xs => SOME (x :: xs)
          | NONE    => NONE)
(* utility functions for string manipulation and printing S76a *)
fun println  s = (print s; print "\n")
fun eprint   s = TextIO.output (TextIO.stdErr, s)
fun eprintln s = (eprint s; eprint "\n")
(* utility functions for string manipulation and printing S76b *)
val xprinter = ref print
fun xprint   s = !xprinter s
fun xprintln s = (xprint s; xprint "\n")
(* utility functions for string manipulation and printing S76c *)
fun tryFinally f x post =
  (f x handle e => (post (); raise e)) before post ()

fun withXprinter xp f x =
  let val oxp = !xprinter
      val ()  = xprinter := xp
  in  tryFinally f x (fn () => xprinter := oxp)
  end
(* utility functions for string manipulation and printing S76d *)
fun bprinter () =
  let val buffer = ref []
      fun bprint s = buffer := s :: !buffer
      fun contents () = concat (rev (!buffer))
  in  (bprint, contents)
  end
(* utility functions for string manipulation and printing S76e *)
fun predefinedFunctionError s = eprintln ("while reading predefined functions, "
                                                                            ^ s)
(* utility functions for string manipulation and printing S77a *)
fun intString n =
  String.map (fn #"~" => #"-" | c => c) (Int.toString n)
(* utility functions for string manipulation and printing S77b *)
fun plural what [x] = what
  | plural what _   = what ^ "s"

fun countString xs what =
  intString (length xs) ^ " " ^ plural what xs
(* utility functions for string manipulation and printing S77c *)
fun separate (zero, sep) = 
  (* list with separator *)
  let fun s []     = zero
        | s [x]    = x
        | s (h::t) = h ^ sep ^ s t
  in  s
end
val spaceSep = separate ("", " ")   (* list separated by spaces *)
val commaSep = separate ("", ", ")  (* list separated by commas *)
(* type declarations for consistency checking *)
val _ = op intString : int -> string
(* type declarations for consistency checking *)
val _ = op spaceSep :                    string list -> string
val _ = op commaSep :                    string list -> string
val _ = op separate : string * string -> string list -> string
(* utility functions for string manipulation and printing S78a *)
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
(* utility functions for string manipulation and printing S78b *)
fun fnvHash s =
  let val offset_basis = 0wx011C9DC5 : Word.word  (* trim the high bit *)
      val fnv_prime    = 0w16777619  : Word.word
      fun update (c, hash) = Word.xorb (hash, Word.fromInt (ord c)) * fnv_prime
      fun int w = Word.toIntX w handle Overflow => Word.toInt (Word.andb (w,
                                                                     0wxffffff))
  in  int (foldl update offset_basis (explode s))
  end
(* type declarations for consistency checking *)
val _ = op fnvHash : string -> int
(* utility functions for string manipulation and printing S79a *)
fun stripNumericSuffix s =
      let fun stripPrefix []         = s   (* don't let things get empty *)
            | stripPrefix (#"-"::[]) = s
            | stripPrefix (#"-"::cs) = implode (reverse cs)
            | stripPrefix (c   ::cs) = if Char.isDigit c then stripPrefix cs
                                       else implode (reverse (c::cs))
      in  stripPrefix (reverse (explode s))
      end
(* support for representing errors as \ml\ values S82b *)
datatype 'a error = OK of 'a | ERROR of string
(* support for representing errors as \ml\ values S83a *)
infix 1 >>=
fun (OK x)      >>= k  =  k x
  | (ERROR msg) >>= k  =  ERROR msg
(* type declarations for consistency checking *)
val _ = op zip3   : 'a list * 'b list * 'c list -> ('a * 'b * 'c) list
val _ = op unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
(* type declarations for consistency checking *)
val _ = op optionList : 'a option list -> 'a list option
(* type declarations for consistency checking *)
val _ = op >>= : 'a error * ('a -> 'b error) -> 'b error
(* support for representing errors as \ml\ values S83b *)
infix 1 >>=+
fun e >>=+ k'  =  e >>= (OK o k')
(* type declarations for consistency checking *)
val _ = op >>=+ : 'a error * ('a -> 'b) -> 'b error
(* support for representing errors as \ml\ values S84a *)
fun errorList es =
  let fun cons (OK x, OK xs) = OK (x :: xs)
        | cons (ERROR m1, ERROR m2) = ERROR (m1 ^ "; " ^ m2)
        | cons (ERROR m, OK _) = ERROR m
        | cons (OK _, ERROR m) = ERROR m
  in  foldr cons (OK []) es
  end
(* type declarations for consistency checking *)
val _ = op errorList : 'a error list -> 'a list error
(* type [[interactivity]] plus related functions and value S220a *)
datatype input_interactivity = PROMPTING | NOT_PROMPTING
(* type [[interactivity]] plus related functions and value S220b *)
datatype output_interactivity = PRINTING | NOT_PRINTING
(* type [[interactivity]] plus related functions and value S220c *)
type interactivity = 
  input_interactivity * output_interactivity
val noninteractive = 
  (NOT_PROMPTING, NOT_PRINTING)
fun prompts (PROMPTING,     _) = true
  | prompts (NOT_PROMPTING, _) = false
fun prints (_, PRINTING)     = true
  | prints (_, NOT_PRINTING) = false
(* type declarations for consistency checking *)
type interactivity = interactivity
val _ = op noninteractive : interactivity
val _ = op prompts : interactivity -> bool
val _ = op prints  : interactivity -> bool
(* simple implementations of set operations S79b *)
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
(* type declarations for consistency checking *)
type 'a set = 'a set
val _ = op emptyset : 'a set
val _ = op member   : ''a -> ''a set -> bool
val _ = op insert   : ''a     * ''a set  -> ''a set
val _ = op union    : ''a set * ''a set  -> ''a set
val _ = op inter    : ''a set * ''a set  -> ''a set
val _ = op diff     : ''a set * ''a set  -> ''a set
(* collections with mapping and combining functions S79c *)
datatype 'a collection = C of 'a set
fun elemsC (C xs) = xs
fun singleC x     = C [x]
val emptyC        = C []
(* type declarations for consistency checking *)
type 'a collection = 'a collection
val _ = op elemsC  : 'a collection -> 'a set
val _ = op singleC : 'a -> 'a collection
val _ = op emptyC  :       'a collection
(* collections with mapping and combining functions S80a *)
fun joinC     (C xs) = C (List.concat (map elemsC xs))
fun mapC  f   (C xs) = C (map f xs)
fun filterC p (C xs) = C (List.filter p xs)
fun mapC2 f (xc, yc) = joinC (mapC (fn x => mapC (fn y => f (x, y)) yc) xc)
(* type declarations for consistency checking *)
val _ = op joinC   : 'a collection collection -> 'a collection
val _ = op mapC    : ('a -> 'b)      -> ('a collection -> 'b collection)
val _ = op filterC : ('a -> bool)    -> ('a collection -> 'a collection)
val _ = op mapC2   : ('a * 'b -> 'c) -> ('a collection * 'b collection -> 'c
                                                                     collection)
(* suspensions S89a *)
datatype 'a action
  = PENDING  of unit -> 'a
  | PRODUCED of 'a

type 'a susp = 'a action ref
(* type declarations for consistency checking *)
type 'a susp = 'a susp
(* suspensions S89b *)
fun delay f = ref (PENDING f)
fun demand cell =
  case !cell
    of PENDING f =>  let val result = f ()
                     in  (cell := PRODUCED result; result)
                     end
     | PRODUCED v => v
(* type declarations for consistency checking *)
val _ = op delay  : (unit -> 'a) -> 'a susp
val _ = op demand : 'a susp -> 'a
(* streams S90a *)
datatype 'a stream 
  = EOS
  | :::       of 'a * 'a stream
  | SUSPENDED of 'a stream susp
infixr 3 :::
(* streams S90b *)
fun streamGet EOS = NONE
  | streamGet (x ::: xs)    = SOME (x, xs)
  | streamGet (SUSPENDED s) = streamGet (demand s)
(* streams S90c *)
fun streamOfList xs = 
  foldr (op :::) EOS xs
(* type declarations for consistency checking *)
val _ = op streamGet : 'a stream -> ('a * 'a stream) option
(* type declarations for consistency checking *)
val _ = op streamOfList : 'a list -> 'a stream
(* streams S90d *)
fun listOfStream xs =
  case streamGet xs
    of NONE => []
     | SOME (x, xs) => x :: listOfStream xs
(* streams S90e *)
fun delayedStream action = 
  SUSPENDED (delay action)
(* type declarations for consistency checking *)
val _ = op listOfStream : 'a stream -> 'a list
(* type declarations for consistency checking *)
val _ = op delayedStream : (unit -> 'a stream) -> 'a stream
(* streams S91a *)
fun streamOfEffects action =
  delayedStream (fn () => case action () of NONE   => EOS
                                          | SOME a => a ::: streamOfEffects
                                                                         action)
(* type declarations for consistency checking *)
val _ = op streamOfEffects : (unit -> 'a option) -> 'a stream
(* streams S91b *)
type line = string
fun filelines infile = 
  streamOfEffects (fn () => TextIO.inputLine infile)
(* type declarations for consistency checking *)
type line = line
val _ = op filelines : TextIO.instream -> line stream
(* streams S91c *)
fun streamRepeat x =
  delayedStream (fn () => x ::: streamRepeat x)
(* type declarations for consistency checking *)
val _ = op streamRepeat : 'a -> 'a stream
(* streams S91d *)
fun streamOfUnfold next state =
  delayedStream (fn () => case next state
                            of NONE => EOS
                             | SOME (a, state') => a ::: streamOfUnfold next
                                                                         state')
(* type declarations for consistency checking *)
val _ = op streamOfUnfold : ('b -> ('a * 'b) option) -> 'b -> 'a stream
(* streams S91e *)
val naturals = 
  streamOfUnfold (fn n => SOME (n, n+1)) 0   (* 0 to infinity *)
(* type declarations for consistency checking *)
val _ = op naturals : int stream
(* streams S92a *)
fun preStream (pre, xs) = 
  streamOfUnfold (fn xs => (pre (); streamGet xs)) xs
(* streams S92b *)
fun postStream (xs, post) =
  streamOfUnfold (fn xs => case streamGet xs
                             of NONE => NONE
                              | head as SOME (x, _) => (post x; head)) xs
(* type declarations for consistency checking *)
val _ = op preStream : (unit -> unit) * 'a stream -> 'a stream
(* type declarations for consistency checking *)
val _ = op postStream : 'a stream * ('a -> unit) -> 'a stream
(* streams S92c *)
fun streamMap f xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => f x ::: streamMap f xs)
(* type declarations for consistency checking *)
val _ = op streamMap : ('a -> 'b) -> 'a stream -> 'b stream
(* streams S92d *)
fun streamFilter p xs =
  delayedStream (fn () => case streamGet xs
                            of NONE => EOS
                             | SOME (x, xs) => if p x then x ::: streamFilter p
                                                                              xs
                                               else streamFilter p xs)
(* type declarations for consistency checking *)
val _ = op streamFilter : ('a -> bool) -> 'a stream -> 'a stream
(* streams S93a *)
fun streamFold f z xs =
  case streamGet xs of NONE => z
                     | SOME (x, xs) => streamFold f (f (x, z)) xs
(* type declarations for consistency checking *)
val _ = op streamFold : ('a * 'b -> 'b) -> 'b -> 'a stream -> 'b
(* streams S93b *)
fun streamZip (xs, ys) =
  delayedStream
  (fn () => case (streamGet xs, streamGet ys)
              of (SOME (x, xs), SOME (y, ys)) => (x, y) ::: streamZip (xs, ys)
               | _ => EOS)
(* streams S93c *)
fun streamConcat xss =
  let fun get (xs, xss) =
        case streamGet xs
          of SOME (x, xs) => SOME (x, (xs, xss))
           | NONE => case streamGet xss
                       of SOME (xs, xss) => get (xs, xss)
                        | NONE => NONE
  in  streamOfUnfold get (EOS, xss)
  end
(* type declarations for consistency checking *)
val _ = op streamZip : 'a stream * 'b stream -> ('a * 'b) stream
(* type declarations for consistency checking *)
val _ = op streamConcat : 'a stream stream -> 'a stream
(* streams S93d *)
fun streamConcatMap f xs = streamConcat (streamMap f xs)
(* type declarations for consistency checking *)
val _ = op streamConcatMap : ('a -> 'b stream) -> 'a stream -> 'b stream
(* streams S93e *)
infix 5 @@@
fun xs @@@ xs' = streamConcat (streamOfList [xs, xs'])
(* type declarations for consistency checking *)
val _ = op @@@ : 'a stream * 'a stream -> 'a stream
(* streams S94a *)
fun streamTake (0, xs) = []
  | streamTake (n, xs) =
      case streamGet xs
        of SOME (x, xs) => x :: streamTake (n-1, xs)
         | NONE => []
(* type declarations for consistency checking *)
val _ = op streamTake : int * 'a stream -> 'a list
(* streams S94b *)
fun streamDrop (0, xs) = xs
  | streamDrop (n, xs) =
      case streamGet xs
        of SOME (_, xs) => streamDrop (n-1, xs)
         | NONE => EOS
(* type declarations for consistency checking *)
val _ = op streamDrop : int * 'a stream -> 'a stream
(* stream transformers and their combinators S101a *)
type ('a, 'b) xformer = 
  'a stream -> ('b error * 'a stream) option
(* type declarations for consistency checking *)
type ('a, 'b) xformer = ('a, 'b) xformer
(* stream transformers and their combinators S101b *)
fun pure y = fn xs => SOME (OK y, xs)
(* type declarations for consistency checking *)
val _ = op pure : 'b -> ('a, 'b) xformer
(* stream transformers and their combinators S103a *)
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
(* type declarations for consistency checking *)
val _ = op <*> : ('a, 'b -> 'c) xformer * ('a, 'b) xformer -> ('a, 'c) xformer
(* stream transformers and their combinators S103b *)
infixr 4 <$>
fun f <$> p = pure f <*> p
(* type declarations for consistency checking *)
val _ = op <$> : ('b -> 'c) * ('a, 'b) xformer -> ('a, 'c) xformer
(* stream transformers and their combinators S104a *)
infix 1 <|>
fun t1 <|> t2 = (fn xs => case t1 xs of SOME y => SOME y | NONE => t2 xs) 
(* type declarations for consistency checking *)
val _ = op <|> : ('a, 'b) xformer * ('a, 'b) xformer -> ('a, 'b) xformer
(* stream transformers and their combinators S104b *)
fun pzero _ = NONE
(* stream transformers and their combinators S104c *)
fun anyParser ts = 
  foldr op <|> pzero ts
(* type declarations for consistency checking *)
val _ = op pzero : ('a, 'b) xformer
(* type declarations for consistency checking *)
val _ = op anyParser : ('a, 'b) xformer list -> ('a, 'b) xformer
(* stream transformers and their combinators S105a *)
infix 6 <* *>
fun p1 <*  p2 = curry fst <$> p1 <*> p2
fun p1  *> p2 = curry snd <$> p1 <*> p2

infixr 4 <$
fun v <$ p = (fn _ => v) <$> p
(* type declarations for consistency checking *)
val _ = op <*  : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'b) xformer
val _ = op  *> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
val _ = op <$  : 'b               * ('a, 'c) xformer -> ('a, 'b) xformer
(* stream transformers and their combinators S105b *)
fun one xs = case streamGet xs
               of NONE => NONE
                | SOME (x, xs) => SOME (OK x, xs)
(* type declarations for consistency checking *)
val _ = op one : ('a, 'a) xformer
(* stream transformers and their combinators S105c *)
fun eos xs = case streamGet xs
               of NONE => SOME (OK (), EOS)
                | SOME _ => NONE
(* type declarations for consistency checking *)
val _ = op eos : ('a, unit) xformer
(* stream transformers and their combinators S106a *)
fun peek tx xs =
  case tx xs of SOME (OK y, _) => SOME y
              | _ => NONE
(* type declarations for consistency checking *)
val _ = op peek : ('a, 'b) xformer -> 'a stream -> 'b option
(* stream transformers and their combinators S106b *)
fun rewind tx xs =
  case tx xs of SOME (ey, _) => SOME (ey, xs)
              | NONE => NONE
(* type declarations for consistency checking *)
val _ = op rewind : ('a, 'b) xformer -> ('a, 'b) xformer
(* stream transformers and their combinators S106c *)
fun sat p tx xs =
  case tx xs
    of answer as SOME (OK y, xs) => if p y then answer else NONE
     | answer => answer
(* type declarations for consistency checking *)
val _ = op sat : ('b -> bool) -> ('a, 'b) xformer -> ('a, 'b) xformer
(* stream transformers and their combinators S106d *)
fun eqx y = 
  sat (fn y' => y = y') 
(* type declarations for consistency checking *)
val _ = op eqx : ''b -> ('a, ''b) xformer -> ('a, ''b) xformer
(* stream transformers and their combinators S107a *)
infixr 4 <$>?
fun f <$>? tx =
  fn xs => case tx xs
             of NONE => NONE
              | SOME (ERROR msg, xs) => SOME (ERROR msg, xs)
              | SOME (OK y, xs) =>
                  case f y
                    of NONE => NONE
                     | SOME z => SOME (OK z, xs)
(* type declarations for consistency checking *)
val _ = op <$>? : ('b -> 'c option) * ('a, 'b) xformer -> ('a, 'c) xformer
(* stream transformers and their combinators S107b *)
infix 3 <&>
fun t1 <&> t2 = fn xs =>
  case t1 xs
    of SOME (OK _, _) => t2 xs
     | SOME (ERROR _, _) => NONE    
     | NONE => NONE
(* type declarations for consistency checking *)
val _ = op <&> : ('a, 'b) xformer * ('a, 'c) xformer -> ('a, 'c) xformer
(* stream transformers and their combinators S107c *)
fun notFollowedBy t xs =
  case t xs
    of NONE => SOME (OK (), xs)
     | SOME _ => NONE
(* type declarations for consistency checking *)
val _ = op notFollowedBy : ('a, 'b) xformer -> ('a, unit) xformer
(* stream transformers and their combinators S107d *)
fun many t = 
  curry (op ::) <$> t <*> (fn xs => many t xs) <|> pure []
(* type declarations for consistency checking *)
val _ = op many  : ('a, 'b) xformer -> ('a, 'b list) xformer
(* stream transformers and their combinators S108a *)
fun many1 t = 
  curry (op ::) <$> t <*> many t
(* type declarations for consistency checking *)
val _ = op many1 : ('a, 'b) xformer -> ('a, 'b list) xformer
(* stream transformers and their combinators S108b *)
fun optional t = 
  SOME <$> t <|> pure NONE
(* type declarations for consistency checking *)
val _ = op optional : ('a, 'b) xformer -> ('a, 'b option) xformer
(* stream transformers and their combinators S109a *)
infix 2 <*>!
fun tx_ef <*>! tx_x =
  fn xs => case (tx_ef <*> tx_x) xs
             of NONE => NONE
              | SOME (OK (OK y),      xs) => SOME (OK y,      xs)
              | SOME (OK (ERROR msg), xs) => SOME (ERROR msg, xs)
              | SOME (ERROR msg,      xs) => SOME (ERROR msg, xs)
infixr 4 <$>!
fun ef <$>! tx_x = pure ef <*>! tx_x
(* type declarations for consistency checking *)
val _ = op <*>! : ('a, 'b -> 'c error) xformer * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
val _ = op <$>! : ('b -> 'c error)             * ('a, 'b) xformer -> ('a, 'c)
                                                                         xformer
(* support for source-code locations and located streams S94d *)
type srcloc = string * int
fun srclocString (source, line) =
  source ^ ", line " ^ intString line
(* support for source-code locations and located streams S95a *)
datatype error_format = WITH_LOCATIONS | WITHOUT_LOCATIONS
val toplevel_error_format = ref WITH_LOCATIONS
(* support for source-code locations and located streams S95b *)
fun synerrormsg (source, line) strings =
  if !toplevel_error_format = WITHOUT_LOCATIONS andalso source =
                                                                "standard input"
  then
    concat ("syntax error: " :: strings)
  else    
    concat ("syntax error in " :: srclocString (source, line) :: ": " :: strings
                                                                               )

(* support for source-code locations and located streams S95c *)
exception Located of srcloc * exn
(* support for source-code locations and located streams S95d *)
type 'a located = srcloc * 'a
(* type declarations for consistency checking *)
type srcloc = srcloc
val _ = op srclocString : srcloc -> string
(* type declarations for consistency checking *)
type 'a located = 'a located
(* support for source-code locations and located streams S95e *)
fun atLoc loc f a =
  f a handle e as RuntimeError _ => raise Located (loc, e)
           | e as NotFound _     => raise Located (loc, e)
           (* more handlers for [[atLoc]] S95g *)
           | e as IO.Io _   => raise Located (loc, e)
           | e as Div       => raise Located (loc, e)
           | e as Overflow  => raise Located (loc, e)
           | e as Subscript => raise Located (loc, e)
           | e as Size      => raise Located (loc, e)
           (* more handlers for [[atLoc]] ((type-inference)) S269b *)
           | e as TypeError _          => raise Located (loc, e)
           | e as BugInTypeInference _ => raise Located (loc, e)
(* type declarations for consistency checking *)
val _ = op atLoc : srcloc -> ('a -> 'b) -> ('a -> 'b)
(* support for source-code locations and located streams S95f *)
fun located f (loc, a) = atLoc loc f a
fun leftLocated f ((loc, a), b) = atLoc loc f (a, b)
(* type declarations for consistency checking *)
val _ = op located : ('a -> 'b) -> ('a located -> 'b)
val _ = op leftLocated : ('a * 'b -> 'c) -> ('a located * 'b -> 'c)
(* support for source-code locations and located streams S96a *)
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
(* type declarations for consistency checking *)
val _ = op fillComplaintTemplate : string * srcloc option -> string
(* support for source-code locations and located streams S96b *)
fun errorAt msg loc = 
  ERROR (synerrormsg loc [msg])
(* support for source-code locations and located streams S96c *)
fun locatedStream (streamname, inputs) =
  let val locations = streamZip (streamRepeat streamname, streamDrop (1,
                                                                      naturals))
  in  streamZip (locations, inputs)
  end
(* type declarations for consistency checking *)
val _ = op errorAt : string -> srcloc -> 'a error
(* type declarations for consistency checking *)
val _ = op locatedStream : string * line stream -> line located stream
(* streams that track line boundaries S113a *)
datatype 'a eol_marked
  = EOL of int (* number of the line that ends here *)
  | INLINE of 'a

fun drainLine EOS = EOS
  | drainLine (SUSPENDED s)     = drainLine (demand s)
  | drainLine (EOL _    ::: xs) = xs
  | drainLine (INLINE _ ::: xs) = drainLine xs
(* streams that track line boundaries S113b *)
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
(* type declarations for consistency checking *)
type 'a eol_marked = 'a eol_marked
val _ = op drainLine : 'a eol_marked stream -> 'a eol_marked stream
(* type declarations for consistency checking *)
val _ = op eol      : ('a eol_marked, int) xformer
val _ = op inline   : ('a eol_marked, 'a)  xformer
val _ = op srcloc   : ('a located eol_marked, srcloc) xformer
(* support for lexical analysis S109b *)
type 'a lexer = (char, 'a) xformer
(* type declarations for consistency checking *)
type 'a lexer = 'a lexer
(* support for lexical analysis S109c *)
fun isDelim c =
  Char.isSpace c orelse Char.contains "()[]{};" c
(* type declarations for consistency checking *)
val _ = op isDelim : char -> bool
(* support for lexical analysis S111a *)
val whitespace = many (sat Char.isSpace one)
(* type declarations for consistency checking *)
val _ = op whitespace : char list lexer
(* support for lexical analysis S111b *)
fun intChars isDelim = 
  (curry (op ::) <$> eqx #"-" one <|> pure id) <*> many1 (sat Char.isDigit one)
                                                                              <*
  notFollowedBy (sat (not o isDelim) one)
(* type declarations for consistency checking *)
val _ = op intChars : (char -> bool) -> char list lexer
(* support for lexical analysis S111c *)
fun intFromChars (#"-" :: cs) = 
      intFromChars cs >>=+ Int.~
  | intFromChars cs =
      (OK o valOf o Int.fromString o implode) cs
      handle Overflow => ERROR
                        "this interpreter can't read arbitrarily large integers"
(* type declarations for consistency checking *)
val _ = op intFromChars : char list -> int error
(* support for lexical analysis S111d *)
fun intToken isDelim =
  intFromChars <$>! intChars isDelim
(* type declarations for consistency checking *)
val _ = op intToken : (char -> bool) -> int lexer
(* support for lexical analysis S112a *)
datatype bracket_shape = ROUND | SQUARE | CURLY

fun leftString ROUND  = "("
  | leftString SQUARE = "["
  | leftString CURLY  = "{"
fun rightString ROUND  = ")"
  | rightString SQUARE = "]"
  | rightString CURLY = "}"
(* support for lexical analysis S112b *)
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
(* type declarations for consistency checking *)
type 'a plus_brackets = 'a plus_brackets
val _ = op bracketLexer : 'a lexer -> 'a plus_brackets lexer
(* common parsing code S100 *)
(* combinators and utilities for parsing located streams S113c *)
type ('t, 'a) polyparser = ('t located eol_marked, 'a) xformer
(* combinators and utilities for parsing located streams S114a *)
fun token    stream = (snd <$> inline)      stream
fun noTokens stream = (notFollowedBy token) stream
(* type declarations for consistency checking *)
val _ = op token    : ('t, 't)   polyparser
val _ = op noTokens : ('t, unit) polyparser
(* combinators and utilities for parsing located streams S114b *)
fun @@ p = pair <$> srcloc <*> p
(* type declarations for consistency checking *)
val _ = op @@ : ('t, 'a) polyparser -> ('t, 'a located) polyparser
(* combinators and utilities for parsing located streams S114c *)
infix 0 <?>
fun p <?> what = p <|> errorAt ("expected " ^ what) <$>! srcloc
(* type declarations for consistency checking *)
val _ = op <?> : ('t, 'a) polyparser * string -> ('t, 'a) polyparser
(* combinators and utilities for parsing located streams S115 *)
infix 4 <!>
fun p <!> msg =
  fn tokens => (case p tokens
                  of SOME (OK _, unread) =>
                       (case peek srcloc tokens
                          of SOME loc => SOME (errorAt msg loc, unread)
                           | NONE => NONE)
                   | _ => NONE)
(* type declarations for consistency checking *)
val _ = op <!> : ('t, 'a) polyparser * string -> ('t, 'b) polyparser
(* combinators and utilities for parsing located streams S118d *)
fun nodups (what, context) (loc, names) =
  let fun dup [] = OK names
        | dup (x::xs) = if List.exists (fn y : string => y = x) xs then
                          errorAt (what ^ " " ^ x ^ " appears twice in " ^
                                                                    context) loc
                        else
                          dup xs
  in  dup names
  end
(* type declarations for consistency checking *)
val _ = op nodups : string * string -> srcloc * name list -> name list error
(* transformers for interchangeable brackets S116 *)
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
(* transformers for interchangeable brackets S117 *)
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
(* type declarations for consistency checking *)
type right_result = right_result
val _ = op matchingRight : ('t, right_result) pb_parser
val _ = op scanToClose   : ('t, right_result) pb_parser
val _ = op matchBrackets : string -> bracket_shape located -> 'a -> right_result
                                                                     -> 'a error
(* transformers for interchangeable brackets S118a *)
fun liberalBracket (expected, p) =
  matchBrackets expected <$> sat notCurly left <*> p <*>! matchingRight
fun bracketKeyword (keyword, expected, p) =
  liberalBracket (expected, keyword *> (p <?> expected))
fun bracket (expected, p) =
  liberalBracket (expected, p <?> expected)
fun curlyBracket (expected, p) =
  matchBrackets expected <$> leftCurly <*> (p <?> expected) <*>! matchingRight
(* type declarations for consistency checking *)
val _ = op bracketKeyword : ('t, 'keyword) pb_parser * string * ('t, 'a)
                                                 pb_parser -> ('t, 'a) pb_parser
(* transformers for interchangeable brackets S118b *)
fun usageParser keyword =
  let val left = eqx #"(" one <|> eqx #"[" one
      val getkeyword = left *> (implode <$> many1 (sat (not o isDelim) one))
  in  fn (usage, p) =>
        case getkeyword (streamOfList (explode usage))
          of SOME (OK k, _) => bracketKeyword (keyword k, usage, p)
           | _ => let exception BadUsage of string in raise BadUsage usage end
  end
(* type declarations for consistency checking *)
val _ = op usageParser : (string -> ('t, string) pb_parser) -> string * ('t, 'a)
                                                 pb_parser -> ('t, 'a) pb_parser
(* transformers for interchangeable brackets S118c *)
fun pretoken stream = ((fn PRETOKEN t => SOME t | _ => NONE) <$>? token) stream
(* code used to debug parsers S119a *)
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
(* type declarations for consistency checking *)
val _ = op safeTokens : 'a located eol_marked stream -> 'a list
(* code used to debug parsers S119b *)
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
(* type declarations for consistency checking *)
val _ = op showErrorInput : ('t -> string) -> ('t, 'a) polyparser -> ('t, 'a)
                                                                      polyparser
(* code used to debug parsers S120a *)
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
(* type declarations for consistency checking *)
val _ = op wrapAround : ('t -> string) -> string -> ('t, 'a) polyparser -> ('t,
                                                                  'a) polyparser
(* streams that issue two forms of prompts S120b *)
fun echoTagStream lines = 
  let fun echoIfTagged line =
        if (String.substring (line, 0, 2) = ";#" handle _ => false) then
          print line
        else
          ()
  in  postStream (lines, echoIfTagged)
  end
(* type declarations for consistency checking *)
val _ = op echoTagStream : line stream -> line stream 
(* streams that issue two forms of prompts S121a *)
fun stripAndReportErrors xs =
  let fun next xs =
        case streamGet xs
          of SOME (ERROR msg, xs) => (eprintln msg; next xs)
           | SOME (OK x, xs) => SOME (x, xs)
           | NONE => NONE
  in  streamOfUnfold next xs
  end
(* type declarations for consistency checking *)
val _ = op stripAndReportErrors : 'a error stream -> 'a stream
(* streams that issue two forms of prompts S121b *)
fun lexLineWith lexer =
  stripAndReportErrors o streamOfUnfold lexer o streamOfList o explode
(* type declarations for consistency checking *)
val _ = op lexLineWith : 't lexer -> line -> 't stream
(* streams that issue two forms of prompts S121c *)
fun parseWithErrors parser =
  let fun adjust (SOME (ERROR msg, tokens)) = SOME (ERROR msg, drainLine tokens)
        | adjust other = other
  in  streamOfUnfold (adjust o parser)
  end
(* type declarations for consistency checking *)
val _ = op parseWithErrors : ('t, 'a) polyparser -> 't located eol_marked stream
                                                              -> 'a error stream
(* streams that issue two forms of prompts S121d *)
type prompts   = { ps1 : string, ps2 : string }
val stdPrompts = { ps1 = "-> ", ps2 = "   " }
val noPrompts  = { ps1 = "", ps2 = "" }
(* type declarations for consistency checking *)
type prompts = prompts
val _ = op stdPrompts : prompts
val _ = op noPrompts  : prompts
(* streams that issue two forms of prompts S122 *)
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
(* type declarations for consistency checking *)
val _ = op interactiveParsedStream : 't lexer * ('t, 'a) polyparser -> string *
                                              line stream * prompts -> 'a stream
val _ = op lexAndDecorate : srcloc * line -> 't located eol_marked stream
  in  
      stripAndReportErrors (preStream (setPrompt ps1, xdefs_with_errors))
  end 
(* common parsing code ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
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
(* shared utility functions for initializing interpreters S224c *)
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
(* function application with overflow checking S81b *)
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
(* function [[forward]], for mutual recursion through mutable reference cells S82a *)
fun forward what _ =
  let exception UnresolvedForwardDeclaration of string
  in  raise UnresolvedForwardDeclaration what
  end
exception LeftAsExercise of string



(*****************************************************************)
(*                                                               *)
(*   HINDLEY-MILNER TYPES WITH GENERATED TYPE CONSTRUCTORS       *)
(*                                                               *)
(*****************************************************************)

(* Hindley-Milner types with generated type constructors S308e *)
(* \small [[tycon]], [[freshTycon]], [[eqTycon]], and [[tyconString]] for generated type constructors 536a *)
type tycon_identity = int
(* \small [[tycon]], [[freshTycon]], [[eqTycon]], and [[tyconString]] for generated type constructors 536b *)
type tycon = { printName : name, identity : tycon_identity }
(* \small [[tycon]], [[freshTycon]], [[eqTycon]], and [[tyconString]] for generated type constructors 536c *)
fun eqTycon ({ identity = id, printName = _ }, { identity = id', printName = _ }
                                                                             ) =
  id = id'
(* type declarations for consistency checking *)
val _ = op eqTycon : tycon * tycon -> bool
(* \small [[tycon]], [[freshTycon]], [[eqTycon]], and [[tyconString]] for generated type constructors S294e *)
fun tyconString { identity = _, printName = T } = T
(* \small [[tycon]], [[freshTycon]], [[eqTycon]], and [[tyconString]] for generated type constructors S295a *)
local
  val timesDefined : int env ref = ref emptyEnv
                             (* how many times each tycon is defined *)
in
  fun freshPrintName t =
    let val n = find (t, !timesDefined) handle NotFound _ => 0
        val _ = timesDefined := bind (t, n + 1, !timesDefined)
    in  if n = 0 then t  (* first definition *)
        else t ^ "@{" ^ Int.toString (n+1) ^ "}"
    end
end
(* type declarations for consistency checking *)
val _ = op freshPrintName : string -> string
(* \small [[tycon]], [[freshTycon]], [[eqTycon]], and [[tyconString]] for generated type constructors S295b *)
local
  val nextIdentity = ref 0
  fun freshIdentity () = !nextIdentity before nextIdentity := !nextIdentity + 2
in
  fun freshTycon t = { identity = freshIdentity(), printName = freshPrintName t
                                                                               }
end
(* type declarations for consistency checking *)
val _ = op freshTycon : name -> tycon
(* representation of Hindley-Milner types 455 *)
type tyvar  = name
datatype ty = TYVAR  of tyvar               (* type variable alpha *)
            | TYCON  of tycon               (* type constructor mu *)
            | CONAPP of ty * ty list        (* type-level application *)

datatype type_scheme = FORALL of tyvar list * ty
(* sets of free type variables in Hindley-Milner types 481 *)
fun freetyvars t =
  let fun f (TYVAR v,          ftvs) = insert (v, ftvs)
        | f (TYCON _,          ftvs) = ftvs
        | f (CONAPP (ty, tys), ftvs) = foldl f (f (ty, ftvs)) tys
  in  reverse (f (t, emptyset))
  end  
(* type declarations for consistency checking *)
val _ = op freetyvars : ty -> name set
(* type constructors built into \uml\ and \uhaskell 536d *)
val inttycon  = freshTycon "int"
val symtycon  = freshTycon "sym"
(* type constructors built into \uml\ and \uhaskell S295c *)
val funtycon  = freshTycon "function"
val argstycon = freshTycon "arguments"
(* types built into \uml\ and \uhaskell S295d *)
val inttype = TYCON inttycon
val symtype = TYCON symtycon
(* code to construct and deconstruct function types for \uml S296a *)
fun funtype (args, result) = 
  CONAPP (TYCON funtycon, [CONAPP (TYCON argstycon, args), result])

fun asFuntype (CONAPP (TYCON mu, [CONAPP (_, args), result])) =
      if eqTycon (mu, funtycon) then
        SOME (args, result)
      else
        NONE
  | asFuntype _ = NONE
(* type declarations for consistency checking *)
val _ = op funtype   : ty list * ty -> ty
val _ = op asFuntype : ty -> (ty list * ty) option
(* definition of [[typeString]] for Hindley-Milner types S270b *)
fun typeString tau =
  case asFuntype tau
    of SOME (args, result) => 
         "(" ^ spaceSep (map typeString args) ^ " -> " ^ typeString result ^ ")"
     | NONE =>
         case tau
           of TYCON c => tyconString c
            | TYVAR a => a
            | CONAPP (tau, []) => "(" ^ typeString tau ^ ")"
            | CONAPP (tau, taus) =>
                "(" ^ typeString tau ^ " " ^ spaceSep (map typeString taus) ^
                                                                             ")"
(* shared utility functions on Hindley-Milner types 457 *)
type subst = ty env
fun varsubst theta = 
  (fn a => find (a, theta) handle NotFound _ => TYVAR a)
(* type declarations for consistency checking *)
type subst = subst
val _ = op varsubst : subst -> (name -> ty)
(* shared utility functions on Hindley-Milner types 458a *)
fun tysubst theta =
  let fun subst (TYVAR a) = varsubst theta a
        | subst (TYCON c) = TYCON c
        | subst (CONAPP (tau, taus)) = CONAPP (subst tau, map subst taus)
(* type declarations for consistency checking *)
val _ = op tysubst : subst -> (ty -> ty)
val _ = op subst   :           ty -> ty
  in  subst
  end
(* shared utility functions on Hindley-Milner types 458b *)
fun dom theta = map (fn (a, _) => a) theta
fun compose (theta2, theta1) =
  let val domain  = union (dom theta2, dom theta1)
      val replace = tysubst theta2 o varsubst theta1
  in  map (fn a => (a, replace a)) domain
  end
(* type declarations for consistency checking *)
val _ = op dom     : subst -> name set
val _ = op compose : subst * subst -> subst
(* shared utility functions on Hindley-Milner types ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
fun eqsubst (theta1, theta2) =
  let val domain  = union (dom theta2, dom theta1)
      fun eqOn a = (varsubst theta1 a = varsubst theta2 a)
  in  List.all eqOn domain
  end
(* shared utility functions on Hindley-Milner types 458c *)
fun instantiate (FORALL (formals, tau), actuals) =
  tysubst (bindList (formals, actuals, emptyEnv)) tau
  handle BindListLength => raise BugInTypeInference
                                              "number of types in instantiation"
(* type declarations for consistency checking *)
val _ = op instantiate : type_scheme * ty list -> ty
(* shared utility functions on Hindley-Milner types 458d *)
val idsubst = emptyEnv
(* shared utility functions on Hindley-Milner types 459a *)
infix 7 |-->
fun a |--> (TYVAR a') = if a = a' then idsubst else bind (a, TYVAR a', emptyEnv)
  | a |--> tau        = bind (a, tau, emptyEnv)
(* type declarations for consistency checking *)
val _ = op idsubst : subst
(* type declarations for consistency checking *)
val _ = op |--> : name * ty -> subst
(* shared utility functions on Hindley-Milner types 459b *)
fun eqType (TYVAR a, TYVAR a') = a = a'
  | eqType (TYCON c, TYCON c') = eqTycon (c, c')
  | eqType (CONAPP (tau, taus), CONAPP (tau', taus')) =
      eqType (tau, tau') andalso eqTypes (taus, taus')
  | eqType _ = false
and eqTypes (taus, taus') = ListPair.allEq eqType (taus, taus')
(* type declarations for consistency checking *)
val _ = op eqType : ty * ty -> bool
(* shared utility functions on Hindley-Milner types 483a *)
local
  val n = ref 1
in
  fun freshtyvar _ = TYVAR ("'t" ^ intString (!n) before n := !n + 1)
(* type declarations for consistency checking *)
val _ = op freshtyvar : 'a -> ty
end
(* shared utility functions on Hindley-Milner types 483b *)
fun canonicalize (FORALL (bound, ty)) =
  let fun canonicalTyvarName n =
        if n < 26 then "'" ^ str (chr (ord #"a" + n))
        else "'v" ^ intString (n - 25)
      val free = diff (freetyvars ty, bound)
      fun unusedIndex n =
        if member (canonicalTyvarName n) free then unusedIndex (n+1) else n
      fun newBoundVars (index, [])                = []
        | newBoundVars (index, oldvar :: oldvars) =
            let val n = unusedIndex index
            in  canonicalTyvarName n :: newBoundVars (n+1, oldvars)
            end
      val newBound = newBoundVars (0, bound)
(* type declarations for consistency checking *)
val _ = op canonicalize : type_scheme -> type_scheme
val _ = op newBoundVars : int * name list -> name list
  in  FORALL (newBound, tysubst (bindList (bound, map TYVAR newBound, emptyEnv))
                                                                             ty)
  end
(* shared utility functions on Hindley-Milner types 483c *)
fun generalize (tau, tyvars) =
  canonicalize (FORALL (diff (freetyvars tau, tyvars), tau))
(* type declarations for consistency checking *)
val _ = op generalize : ty * name set -> type_scheme
(* shared utility functions on Hindley-Milner types 484 *)
fun freshInstance (FORALL (bound, tau)) =
  instantiate (FORALL (bound, tau), map freshtyvar bound)
(* type declarations for consistency checking *)
val _ = op freshInstance : type_scheme -> ty
(* shared utility functions on Hindley-Milner types S296b *)
datatype scheme_shape
  = MONO_FUN of              ty list * ty    (* (tau1 ... tauN -> tau) *)
  | MONO_VAL of              ty              (* tau *)
  | POLY_FUN of tyvar list * ty list * ty
                                         (* (forall (a ...) (tau ... -> tau)) *)
  | POLY_VAL of tyvar list * ty              (* (forall (a ...) tau) *)
(* shared utility functions on Hindley-Milner types S296c *)
fun schemeShape (FORALL (alphas, tau)) =
  case asFuntype tau
    of NONE => if null alphas then MONO_VAL tau
               else                POLY_VAL (alphas, tau)
     | SOME (args, result) =>
               if null alphas then MONO_FUN (args, result)
               else                POLY_FUN (alphas, args, result)
(* type declarations for consistency checking *)
type scheme_shape = scheme_shape
(* type declarations for consistency checking *)
val _ = op schemeShape : type_scheme -> scheme_shape
(* shared utility functions on Hindley-Milner types S271a *)
fun typeSchemeString (FORALL ([], tau)) =
      typeString tau
  | typeSchemeString (FORALL (a's, tau)) =
      "(forall (" ^ spaceSep a's ^ ") " ^ typeString tau ^ ")"
(* type declarations for consistency checking *)
val _ = op typeString       : ty          -> string
val _ = op typeSchemeString : type_scheme -> string
(* shared utility functions on Hindley-Milner types ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
fun substString pairs =
      separate ("idsubst", " o ")
      (map (fn (a, t) => a ^ " |--> " ^ typeString t) pairs)
(* specialized environments for type schemes 485a *)
type type_env = type_scheme env * name set
(* specialized environments for type schemes 485b *)
val emptyTypeEnv = 
      (emptyEnv, emptyset)
fun findtyscheme (x, (Gamma, free)) = find (x, Gamma)
(* type declarations for consistency checking *)
val _ = op emptyTypeEnv : type_env
val _ = op findtyscheme : name * type_env -> type_scheme
(* specialized environments for type schemes 485c *)
fun bindtyscheme (x, sigma as FORALL (bound, tau), (Gamma, free)) = 
  (bind (x, sigma, Gamma), union (diff (freetyvars tau, bound), free))
(* specialized environments for type schemes 485d *)
fun freetyvarsGamma (_, free) = free
(* specialized environments for type schemes S303c *)
fun extendTypeEnv (Gamma, bindings) =
  let fun add ((x, sigma), Gamma) = bindtyscheme (x, sigma, Gamma)
  in  foldl add Gamma bindings
  end
(* type declarations for consistency checking *)
val _ = op extendTypeEnv : type_env * type_scheme env -> type_env
(* extensions that support existential types S309a *)
datatype x_type_scheme
  = FORALL_EXISTS of tyvar list * tyvar list * ty list * ty

fun asExistential (FORALL (alphas_and_betas, tau)) =
  let fun asTyvar (TYVAR a) = a
        | asTyvar _ = let exception GADT in raise GADT end
      fun typeParameters (CONAPP (mu, alphas)) = map asTyvar alphas
        | typeParameters _ = []
  in  case asFuntype tau
        of SOME (args, result) =>
             let val alphas = typeParameters result
                 val betas = diff (alphas_and_betas, alphas)
             in  SOME (FORALL_EXISTS (alphas, betas, args, result))
             end
         | NONE => NONE
  end
(* type declarations for consistency checking *)
type x_type_scheme = x_type_scheme
val _ = op asExistential : type_scheme -> x_type_scheme option
(* extensions that support existential types S309b *)
fun freshSkolem _ =
  let val { identity = id, printName = T } = freshTycon "skolem type"
  in  TYCON { identity = id + 1, printName = "skolem type " ^ intString (id div
                                                                            2) }
  end

fun isSkolem { identity = n, printName = _ } = (n mod 2 = 1)
(* extensions that support existential types S311a *)
fun addFreeSkolems (TYCON mu, mus) =
      if isSkolem mu then insert (mu, mus) else mus
  | addFreeSkolems (TYVAR _,  mus) =
      mus
  | addFreeSkolems (CONAPP (tau, taus), mus) =
      foldl addFreeSkolems (addFreeSkolems (tau, mus)) taus
(* extensions that support existential types S311b *)
fun typeFreeSkolems        tau    = addFreeSkolems (tau, emptyset)
fun typesFreeSkolems       taus   = foldl addFreeSkolems emptyset taus
fun typeSchemesFreeSkolems sigmas =
      typesFreeSkolems (map (fn FORALL (_, tau) => tau) sigmas)
(* type declarations for consistency checking *)
val _ = op addFreeSkolems : ty * tycon set -> tycon set
(* type declarations for consistency checking *)
val _ = op typeFreeSkolems  : ty     -> tycon set
val _ = op typesFreeSkolems : ty set -> tycon set
val _ = op typeSchemesFreeSkolems : type_scheme list -> tycon set
(* extensions that support existential types S311c *)
fun typeEnvSubst theta Gamma' =
  let fun subst (FORALL ([], tau)) = FORALL ([], tysubst theta tau)
        | subst _ = let exception PolytypeInPattern in raise PolytypeInPattern
                                                                             end
  in  map (fn (x, sigma) => (x, subst sigma)) Gamma'
  end



(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES FOR \UML                         *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values for \uml S294d *)
(* kinds for typed languages 396a *)
datatype kind = TYPE                          (* kind of all types *)
              | ARROW of kind list * kind     (* kind of many constructors *)
(* kinds for typed languages 396b *)
fun eqKind (TYPE, TYPE) = true
  | eqKind (ARROW (args, result), ARROW (args', result')) =
      eqKinds (args, args') andalso eqKind (result, result')
  | eqKind (_, _) = false
and eqKinds (ks, ks') = ListPair.allEq eqKind (ks, ks')
(* kinds for typed languages (BUG: software can't tell where this code came from [NW4fx3pn-2bdUVX-1]) *)
fun kindString TYPE = "*"
  | kindString (ARROW (ks, k)) =
      "(" ^ spaceSep (map kindString ks @ ["=>", kindString k]) ^ ")"
(* definition of [[tyex]] for \uml S299a *)
datatype tyex = TYNAME  of name
                                            (* names type or type constructor *)
              | CONAPPX of tyex * tyex list    (* type-level application *)
              | FUNTYX  of tyex list * tyex
              | FORALLX of name list * tyex
              | TYVARX  of name                (* type variable *)
(* definition of [[pat]], for patterns 537c *)
type vcon = name   (* a value constructor *)  (*OMIT*)
datatype pat = WILDCARD
             | PVAR     of name
             | CONPAT   of vcon * pat list
(* definitions of [[exp]] and [[value]] for \uml 537a *)
type vcon = name   (* a value constructor *)
datatype exp 
  = VCONX of vcon
  | CASE  of exp * (pat * exp) list
  | (* forms of [[exp]] carried over from \nml S294a *)
        LITERAL    of value
      | VAR        of name
      | IFX        of exp * exp * exp (* could be syntactic sugar for CASE *)
      | BEGIN      of exp list
      | APPLY      of exp * exp list
      | LETX       of let_kind * (name * exp) list * exp
      | LAMBDA     of name list * exp
    and let_kind = LET | LETREC | LETSTAR
(* definitions of [[exp]] and [[value]] for \uml 537d *)
and value
  = CONVAL of vcon * value list
  | SYM    of name
  | NUM    of int
  | CLOSURE   of lambda * (unit -> value env)
  | PRIMITIVE of primop
 withtype lambda = name list * exp
      and primop = value list -> value
(* definition of [[def]] for \uml 537b *)
datatype def = DATA of data_def
             | (* forms of [[def]] carried over from \nml S294b *)
                 VAL    of name * exp
               | VALREC of name * exp
               | EXP    of exp
               | DEFINE of name * (name list * exp)
  withtype data_def = name * kind * (vcon * tyex) list
(* type declarations for consistency checking *)
type data_def = data_def
(* definition of [[implicit_data_def]] for \uml S331b *)
datatype implicit_data_def 
  = IMPLICIT_DATA of tyvar list * name * implicit_vcon list
and implicit_vcon 
  = IMPLICIT_VCON of vcon * tyex list
(* definition of [[unit_test]] for languages with Hindley-Milner types and generated type constructors S294c *)
datatype unit_test = CHECK_EXPECT      of exp * exp
                   | CHECK_ASSERT      of exp
                   | CHECK_ERROR       of exp
                   | CHECK_TYPE        of exp * tyex
                   | CHECK_PTYPE       of exp * tyex
                   | CHECK_TYPE_ERROR  of def
(* definition of [[xdef]] (shared) S217b *)
datatype xdef = DEF    of def
              | USE    of name
              | TEST   of unit_test
              | DEFS   of def list  (*OMIT*)
(* definition of [[valueString]] for \uml S325b *)

fun valueString (CONVAL ("cons", [v, vs])) = consString (v, vs)
  | valueString (CONVAL ("'()",  []))      = "()"
  | valueString (CONVAL (c, []))  = c
  | valueString (CONVAL (c, vs))  =
      "(" ^ c ^ " " ^ spaceSep (map valueString vs) ^ ")"
  | valueString (NUM n      )   = String.map (fn #"~" => #"-" | c => c) (
                                                                 Int.toString n)
  | valueString (SYM v      )   = v
  | valueString (CLOSURE   _)   = "<procedure>"
  | valueString (PRIMITIVE _)   = "<procedure>"
(* definition of [[valueString]] for \uml S325c *)
and consString (v, vs) =
      let fun tail (CONVAL ("cons", [v, vs])) = " " ^ valueString v ^ tail vs
            | tail (CONVAL ("'()", []))       = ")"
            | tail _ =
                raise BugInTypeInference
                  "bad list constructor (or cons/'() redefined)"
      in  "(" ^ valueString v ^ tail vs
	  end
(* type declarations for consistency checking *)
val _ = op valueString : value -> string
(* definition of [[patString]] for \uml\ and \uhaskell ((uml)) S325e *)
fun patString WILDCARD    = "_"
  | patString (PVAR x)    = x
  | patString (CONPAT (vcon, []))   = vcon
  | patString (CONPAT (vcon, pats)) = "(" ^ spaceSep (vcon :: map patString pats
                                                                         ) ^ ")"
(* definition of [[expString]] for \nml\ and \uml S276a *)
fun expString e =
  let fun bracket s = "(" ^ s ^ ")"
      fun sqbracket s = "[" ^ s ^ "]"
      val bracketSpace = bracket o spaceSep
      fun exps es = map expString es
      fun withBindings (keyword, bs, e) =
        bracket (spaceSep [keyword, bindings bs, expString e])
      and bindings bs = bracket (spaceSep (map binding bs))
      and binding (x, e) = sqbracket (x ^ " " ^ expString e)
      val letkind = fn LET => "let" | LETSTAR => "let*" | LETREC => "letrec"
  in  case e
        of LITERAL v => valueString v
         | VAR name => name
         | IFX (e1, e2, e3) => bracketSpace ("if" :: exps [e1, e2, e3])
         | BEGIN es => bracketSpace ("begin" :: exps es)
         | APPLY (e, es) => bracketSpace (exps (e::es))
         | LETX (lk, bs, e) => bracketSpace [letkind lk, bindings bs, expString
                                                                              e]
         | LAMBDA (xs, body) => bracketSpace ["lambda",
                                              bracketSpace xs, expString body]
         (* extra cases of [[expString]] for \uml S325d *)
         | VCONX vcon => vcon
         | CASE (e, matches) =>
             let fun matchString (pat, e) = sqbracket (spaceSep [patString pat,
                                                                   expString e])
             in  bracketSpace ("case" :: expString e :: map matchString matches)
             end
         (* extra cases of [[expString]] for \uml S276b *)
         (* this space is filled in by the uML appendix *)
  end
(* definitions of [[defString]] and [[defName]] for \nml\ and \uml S276c *)
fun defString d =
  let fun bracket s = "(" ^ s ^ ")"
      val bracketSpace = bracket o spaceSep
      fun formal (x, t) = "[" ^ x ^ " : " ^ typeString t ^ "]"
  in  case d
        of EXP e         => expString e
         | VAL    (x, e) => bracketSpace ["val",     x, expString e]
         | VALREC (x, e) => bracketSpace ["val-rec", x, expString e]
         | DEFINE (f, (formals, body)) =>
             bracketSpace ["define", f, bracketSpace formals, expString body]

(* cases for [[defString]] for forms found only in \uml ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
         | DATA (t, kind, _) => bracketSpace ["data", kindString kind, t, "..."]

(* cases for [[defString]] for forms found only in \uml ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
         (*empty*)
  end
fun defName (VAL (x, _))       = x
  | defName (VALREC (x, _)) = x
  | defName (DEFINE (x, _)) = x
  | defName (EXP _) = raise InternalError "asked for name defined by expression"

(* clauses for [[defName]] for forms found only in \uml ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
  | defName (DATA (t, _, _)) = t

(* clauses for [[defName]] for forms found only in \uml ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
  (*empty*)
(* definition of [[tyexString]] for \uml S326b *)
fun tyexString (TYNAME t) = t
  | tyexString (CONAPPX (tx, txs)) =
      "(" ^ tyexString tx ^ " " ^ spaceSep (map tyexString txs) ^ ")"
  | tyexString (FORALLX (alphas, tx)) =
      "(forall (" ^ spaceSep alphas ^ ") " ^ tyexString tx ^ ")"
  | tyexString (TYVARX a) = a
  | tyexString (FUNTYX (args, result)) =
      "(" ^ spaceSep (map tyexString args) ^ " -> " ^ tyexString result ^ ")"


(*****************************************************************)
(*                                                               *)
(*   UTILITY FUNCTIONS ON \UML\ SYNTAX                           *)
(*                                                               *)
(*****************************************************************)

(* utility functions on \uml\ syntax S302d *)
fun isfuntype (FORALLX (_, tau)) = isfuntype tau
  | isfuntype (FUNTYX _)         = true
  | isfuntype _                  = false


(*****************************************************************)
(*                                                               *)
(*   UTILITY FUNCTIONS ON \UML\ VALUES                           *)
(*                                                               *)
(*****************************************************************)

(* utility functions on \uml\ values ((uml)) S307a *)
fun primitiveEquality (v, v') =
  let fun noFun () = raise RuntimeError "compared functions for equality"
  in  case (v, v')
        of (NUM  n1,  NUM  n2)  => (n1 = n2)
         | (SYM  v1,  SYM  v2)  => (v1 = v2)
         | (CONVAL (vcon, vs), CONVAL (vcon', vs')) =>
             vcon = vcon' andalso ListPair.allEq primitiveEquality (vs, vs')
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
(* utility functions on \uml\ values ((uml)) S308a *)
fun embedList []      = CONVAL ("'()", [])
  | embedList (v::vs) = CONVAL ("cons", [v, embedList vs])
(* type declarations for consistency checking *)
val _ = op embedList : value list -> value
(* utility functions on \uml\ values ((uml)) S308c *)
fun embedBool b = CONVAL (if b then "#t" else "#f", [])
fun bool (CONVAL ("#t", [])) = true
  | bool _                   = false
(* type declarations for consistency checking *)
val _ = op bool      : value -> bool
val _ = op embedBool : bool -> value



(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS AND PARSING FOR \UML, PROVIDING [[FILEXDEFS]] AND [[STRINGSXDEFS]] *)
(*                                                               *)
(*****************************************************************)

(* lexical analysis and parsing for \uml, providing [[filexdefs]] and [[stringsxdefs]] S311e *)
(* lexical analysis for \uscheme\ and related languages S226a *)
datatype pretoken = QUOTE
                  | INT     of int
                  | SHARP   of bool
                  | NAME    of string
type token = pretoken plus_brackets
(* lexical analysis for \uscheme\ and related languages S226b *)
fun pretokenString (QUOTE)     = "'"
  | pretokenString (INT  n)    = intString n
  | pretokenString (SHARP b)   = if b then "#t" else "#f"
  | pretokenString (NAME x)    = x
val tokenString = plusBracketsString pretokenString
(* lexical analysis for \uscheme\ and related languages S226c *)
local
  (* functions used in all lexers S227a *)
  fun noneIfLineEnds chars =
    case streamGet chars
      of NONE => NONE (* end of line *)
       | SOME (#";", cs) => NONE (* comment *)
       | SOME (c, cs) => 
           let val msg = "invalid initial character in `" ^
                         implode (c::listOfStream cs) ^ "'"
           in  SOME (ERROR msg, EOS)
           end
  (* type declarations for consistency checking *)
  val _ = op noneIfLineEnds : 'a lexer
  (* functions used in the lexer for \uscheme S226d *)
  fun atom "#t" = SHARP true
    | atom "#f" = SHARP false
    | atom x    = NAME x
in
  val schemeToken =
    whitespace *>
    bracketLexer   (  QUOTE   <$  eqx #"'" one
                  <|> INT     <$> intToken isDelim
                  <|> (atom o implode) <$> many1 (sat (not o isDelim) one)
                  <|> noneIfLineEnds
                   )
(* type declarations for consistency checking *)
val _ = op schemeToken : token lexer
val _ = op atom : string -> pretoken
end
(* parsers for single \uscheme\ tokens S227b *)
type 'a parser = (token, 'a) polyparser
val pretoken  = (fn (PRETOKEN t)=> SOME t  | _ => NONE) <$>? token : pretoken
                                                                          parser
val quote     = (fn (QUOTE)     => SOME () | _ => NONE) <$>? pretoken
val int       = (fn (INT   n)   => SOME n  | _ => NONE) <$>? pretoken
val booltok   = (fn (SHARP b)   => SOME b  | _ => NONE) <$>? pretoken
val name      = (fn (NAME  n)   => SOME n  | _ => NONE) <$>? pretoken
val any_name  = name
(* parsers for \uml\ tokens S312c *)
val tyvar = quote *> (curry op ^ "'" <$> name <?>
                                               "type variable (got quote mark)")
val any_name = name
val name = () (* don't use me as a parser *)
(* parsers for \uml\ value constructors and value variables S312d *)
fun isVcon x =
  let val first = String.sub (x, 0)
  in  x = "cons" orelse x = "'()" orelse
      Char.isUpper first orelse first = #"#" orelse
      String.isPrefix "make-" x
  end
fun isVvar x = x <> "->" andalso not (isVcon x)
(* parsers for \uml\ value constructors and value variables S313a *)
val arrow = sat (fn n => n = "->") any_name
val vvar  = sat isVvar any_name
val tyname = vvar
val vcon  = 
  let fun isEmptyList (left, right) = notCurly left andalso snd left = snd right
      val boolcon  = (fn p => if p then "#t" else "#f") <$> booltok
  in  boolcon <|> sat isVcon any_name <|>
      "'()" <$ quote <* sat isEmptyList (pair <$> left <*> right)
  end
(* parsers and parser builders for formal parameters and bindings S228a *)
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
(* type declarations for consistency checking *)
val _ = op formalsOf  : string -> name parser -> string -> name list parser
val _ = op bindingsOf : string -> 'x parser -> 'e parser -> ('x * 'e) list
                                                                          parser
val _ = op distinctBsIn : (name * 'e) list parser -> string -> (name * 'e) list
                                                                          parser
(* parsers and parser builders for formal parameters and bindings S228b *)
fun recordFieldsOf name =
  nodups ("record fields", "record definition") <$>!
                                    @@ (bracket ("(field ...)", many name))
(* type declarations for consistency checking *)
val _ = op recordFieldsOf : name parser -> name list parser
(* parsers and parser builders for formal parameters and bindings S228c *)
fun kw keyword = 
  eqx keyword any_name
fun usageParsers ps = anyParser (map (usageParser kw) ps)
(* type declarations for consistency checking *)
val _ = op kw : string -> string parser
val _ = op usageParsers : (string * 'a parser) list -> 'a parser
(* parsers and parser builders for \scheme-like syntax S228d *)
fun sexp tokens = (
     SYM       <$> (notDot <$>! @@ any_name)
 <|> NUM       <$> int
 <|> embedBool <$> booltok
 <|> leftCurly <!> "curly brackets may not be used in S-expressions"
 <|> embedList <$> bracket ("list of S-expressions", many sexp)
 <|> (fn v => embedList [SYM "quote", v]) 
               <$> (quote *> sexp)
) tokens
and notDot (loc, ".") =
      errorAt "this interpreter cannot handle . in quoted S-expressions" loc
  | notDot (_,   s)   = OK s
(* type declarations for consistency checking *)
val _ = op sexp : value parser
(* parsers and parser builders for \scheme-like syntax S229a *)
fun atomicSchemeExpOf name =  VAR                   <$> name
                          <|> LITERAL <$> NUM       <$> int
                          <|> LITERAL <$> embedBool <$> booltok
(* parsers and parser builders for \scheme-like syntax S229d *)
fun fullSchemeExpOf atomic keywordsOf =
  let val exp = fn tokens => fullSchemeExpOf atomic keywordsOf tokens
  in      atomic
      <|> keywordsOf exp
      <|> quote *> (LITERAL <$> sexp)
      <|> quote *> badRight "quote ' followed by right bracket"
      <|> leftCurly <!> "curly brackets are not supported"
      <|> left *> right <!> "(): unquoted empty parentheses"
      <|> bracket("function application", curry APPLY <$> exp <*> many exp)
  end
(* parser builders for typed languages S252e *)
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
(* parser builders for typed languages S242b *)
fun typedFormalOf name colon ty =
      bracket ("[x : ty]", pair <$> name <* colon <*> ty)
fun typedFormalsOf name colon ty context = 
  let val formal = typedFormalOf name colon ty
  in  distinctBsIn (bracket("(... [x : ty] ...)", many formal)) context
  end                            
(* type declarations for consistency checking *)
val _ = op typedFormalsOf : string parser -> 'b parser -> 'a parser -> string ->
                                                       (string * 'a) list parser
(* parsers for Hindley-Milner types with generated type constructors S312a *)
fun tyex tokens = (
     TYNAME <$> tyname
 <|> TYVARX <$> tyvar
 <|> usageParsers
           [("(forall (tyvars) type)",
             curry FORALLX <$> bracket ("('a ...)", distinctTyvars) <*> tyex)]
 <|> bracket("(ty ty ... -> ty)",
             arrowsOf CONAPPX FUNTYX <$> many tyex <*>! many (arrow *> many tyex
                                                                              ))
) tokens
(* type declarations for consistency checking *)
val _ = op typeEnvSubst : subst -> type_scheme env -> type_scheme env
(* type declarations for consistency checking *)
val _ = op tyvar : string parser
val _ = op tyex  : tyex   parser
(* parsers for Hindley-Milner types with generated type constructors S312b *)
fun kind tokens = (
  TYPE <$ eqx "*" vvar
  <|> bracket ("arrow kind", curry ARROW <$> many kind <* eqx "=>" vvar <*> kind
                                                                               )
) tokens

val kind = kind <?> "kind"
(* type declarations for consistency checking *)
val _ = op kind : kind parser
(* parsers and [[xdef]] streams for \uml S313b *)
fun pattern tokens =  (
                WILDCARD    <$  eqx "_" vvar
      <|>       PVAR        <$> vvar
      <|> curry CONPAT      <$> vcon <*> pure []
      <|> bracket ( "(C x1 x2 ...) in pattern"
                  , curry CONPAT <$> vcon <*> many pattern
                  )
       ) tokens
(* type declarations for consistency checking *)
val _ = op pattern : pat parser
(* parsers and [[xdef]] streams for \uml S313c *)
val vvarFormalsIn = formalsOf "(x1 x2 ...)" vvar
val patFormals    = bracket ("(p1 p2 ...)", many pattern)
(* type declarations for consistency checking *)
val _ = op vvarFormalsIn : string -> name list parser
val _ = op patFormals    :            pat list parser
(* parsers and [[xdef]] streams for \uml S314 *)
(* utility functions that help implement \uml's syntactic sugar ((prototype)) S317e *)
fun freeIn exp y =
  let fun has_y (CASE (e, choices)) = has_y e orelse (List.exists choice_has_y)
                                                                         choices
        | has_y _ = raise LeftAsExercise "free variable of an expression"
      and choice_has_y (p, e) = not (pat_has_y p) andalso has_y e
      and pat_has_y (PVAR x) = x = y
        | pat_has_y (CONPAT (_, ps)) = List.exists pat_has_y ps
        | pat_has_y WILDCARD = false
  in  has_y exp
  end
(* utility functions that help implement \uml's syntactic sugar S318a *)
val varsupply = 
  streamMap (fn n => "x" ^ intString n) naturals
fun freshVar e =
  case streamGet (streamFilter (not o freeIn e) varsupply)
    of SOME (x, _) => x
     | NONE => let exception EmptyVarSupply in raise EmptyVarSupply end
(* type declarations for consistency checking *)
val _ = op freeIn : exp -> name -> bool
(* type declarations for consistency checking *)
val _ = op varsupply : name stream
val _ = op freshVar  : exp -> name
(* utility functions that help implement \uml's syntactic sugar S318b *)
fun freshVars e xs =
  streamTake (length xs, streamFilter (not o freeIn e) varsupply)
(* type declarations for consistency checking *)
val _ = op freshVars : exp -> 'a list -> name list
(* utility functions that help implement \uml's syntactic sugar S318c *)
fun tupleVcon xs = case length xs
                     of 2 => "PAIR"
                      | 3 => "TRIPLE"
                      | n => "T" ^ intString n

fun tupleexp [x] = VAR x
  | tupleexp xs  = APPLY (VCONX (tupleVcon xs), map VAR xs)

fun tuplepat [x] = x
  | tuplepat xs  = CONPAT (tupleVcon xs, xs)
(* type declarations for consistency checking *)
val _ = op tupleexp  : name list -> exp
val _ = op tuplepat  : pat  list -> pat
val _ = op tupleVcon : 'a   list -> vcon
(* utility functions that help implement \uml's syntactic sugar S318d *)
fun freePatVars (PVAR x)         = insert (x, emptyset)
  | freePatVars (WILDCARD)       = emptyset
  | freePatVars (CONPAT (_, ps)) = foldl union emptyset (map freePatVars ps)
(* type declarations for consistency checking *)
val _ = op freePatVars : pat -> name set
fun exptable exp =
  let (* parsers used in both flavors *)
      val choice   = bracket ("[pattern exp]", pair <$> pattern <*> exp)
      val letrecBs = distinctBsIn (bindingsOf "(x e)" vvar exp) "letrec"

      (* parsers for bindings to names *)
      val letBs     = distinctBsIn (bindingsOf "(x e)" vvar exp) "let"
      val letstarBs = bindingsOf "(x e)" vvar exp
      val formals   = vvarFormalsIn "lambda"

      (* parsers for bindings to patterns *)
      val patBs       = bindingsOf "(p e)" pattern exp
      val patLetrecBs = map (fn (x, e) => (PVAR x, e)) <$> letrecBs
      val patLetBs =
        let fun patVars (WILDCARD)       = []
              | patVars (PVAR x)         = [x]
              | patVars (CONPAT (_, ps)) = List.concat (map patVars ps)
            fun check (loc, bs) =
              let val xs = List.concat (map (patVars o fst) bs)
              in  nodups ("bound name", "let") (loc, xs) >>=+ (fn _ => bs)
              end
        in  check <$>! @@ patBs
        end
      val patFormals = patFormals (* defined above *)

      (* expression builders that expect to bind names *)
      fun letx letkind bs e = LETX (letkind, bs, e)
      fun lambda xs e = LAMBDA (xs, e)
      fun lambdastar clauses = ERROR "lambda* is left as an exercise"

      (* \uml\ expression builders that expect to bind patterns S318e *)
      (* you can redefine letx, lambda, and lambdastar here *)
  in  (* parsers for expressions that begin with keywords S315a *)
      usageParsers
        [ ("(if e1 e2 e3)",            curry3 IFX    <$> exp  <*> exp <*> exp)
        , ("(begin e1 ...)",                  BEGIN  <$> many exp)
        , ("(lambda (names) body)",           lambda <$> formals <*> exp)
        , ("(lambda* (pats) exp ...)",
             lambdastar <$>!
             many1 (bracket ("[(pat ...) e]",
                             pair <$> (bracket ("(pat ...)", many pattern)) <*>
                                                                          exp)))
        , ("(let (bindings) body)",    letx   LET     <$> letBs     <*> exp)
        , ("(letrec (bindings) body)", letx   LETREC  <$> letrecBs  <*> exp)
        , ("(let* (bindings) body)",   letx   LETSTAR <$> letstarBs <*> exp)
        , ("(case exp [pattern exp] ...)", curry CASE <$> exp <*> many choice)

        , ("(while e1 e2)", exp  *> exp <!>
                                     "uML does not include 'while' expressions")
        , ("(set x e)",     vvar *> exp <!>
                                       "uML does not include 'set' expressions")
        (* rows added to \uml's [[exptable]] in exercises S319d *)
        (* you add this bit *)
        ]
  end
(* parsers and [[xdef]] streams for \uml S315b *)
val atomicExp =  VAR               <$> vvar
             <|> VCONX             <$> vcon
             <|> (LITERAL o NUM)   <$> int

fun exp tokens = (
     atomicExp
 <|> quote *> (LITERAL <$> sexp)
 <|> exptable exp
 <|> leftCurly <!> "curly brackets are not supported"
 <|> left *> right <!> "empty application"
 <|> bracket ("function application", curry APPLY <$> exp <*> many exp)
) tokens
(* type declarations for consistency checking *)
val _ = op atomicExp : exp parser
val _ = op exp       : exp parser
(* parsers and [[xdef]] streams for \uml S316a *)
(* definition of [[makeExplicit]], to translate [[implicit-data]] to [[data]] S332a *)
fun makeExplicit (IMPLICIT_DATA ([], t, vcons)) =
      let val tx = TYNAME t
          fun convertVcon (IMPLICIT_VCON (K, []))  = (K, tx)
            | convertVcon (IMPLICIT_VCON (K, txs)) = (K, FUNTYX (txs, tx))
      in  (t, TYPE, map convertVcon vcons)
      end
  | makeExplicit (IMPLICIT_DATA (alphas, t, vcons)) =
      let val kind = ARROW (map (fn _ => TYPE) alphas, TYPE)
          val tx   = CONAPPX (TYNAME t, map TYVARX alphas)
          fun close tau = FORALLX (alphas, tau)
          fun vconType (vcon, [])  = tx
            | vconType (vcon, txs) = FUNTYX (txs, tx)
          fun convertVcon (IMPLICIT_VCON (K, []))  = (K, close tx)
            | convertVcon (IMPLICIT_VCON (K, txs)) = (K, close (FUNTYX (txs, tx)
                                                                              ))
  in  (t, kind, map convertVcon vcons)
  end
(* type declarations for consistency checking *)
val _ = op makeExplicit : implicit_data_def -> data_def
val tyvarlist = bracket ("('a ...)", many1 tyvar)
val optionalTyvars = (fn alphas => getOpt (alphas, [])) <$> optional tyvarlist
val implicitData =
  let fun vc c taus = IMPLICIT_VCON (c, taus)
      val vconDef =  vc <$> vcon <*> pure []
                 <|> bracket ("(vcon of ty ...)",
                              vc <$> vcon <* eqx "of" vvar <*> many1 tyex)
  in  usageParsers
      [("(implicit-data [('a ...)] t vcon ... (vcon of ty ...) ...)"
       , (DATA o makeExplicit) <$>
         (curry3 IMPLICIT_DATA <$> optionalTyvars <*> tyname <*> many vconDef)
       )]
  end
(* type declarations for consistency checking *)
val _ = op implicitData : def parser
(* parsers and [[xdef]] streams for \uml S316b *)
val def = 
  let (* parser for binding to names *)
      val formals = vvarFormalsIn "define"

      (* parsers for clausal definitions, a.k.a. define* *)
      val lhs = bracket ("(f p1 p2 ...)", pair <$> vvar <*> many pattern)
      val clause =
        bracket ("[(f p1 p2 ...) e]",
                 (fn (f, ps) => fn e => (f, (ps, e))) <$> lhs <*> exp)

      (* definition builders used in all parsers *)
      val Kty = typedFormalOf vcon (kw ":") tyex
      fun data kind name vcons = DATA (name, kind, vcons)

      (* definition builders that expect to bind names *)
      fun define f xs body = DEFINE (f, (xs, body))
      fun definestar _ = ERROR "define* is left as an exercise"


(* \uml\ definition builders that expect to bind patterns ((prototype)) S318f *)
      (* you can redefine 'define' and 'definestar' here *)
  in  usageParsers
      [ ("(define f (args) body)",        define       <$> vvar <*> formals <*>
                                                                            exp)
      , ("(define* (f pats) e ...)",      definestar   <$>! many1 clause)
      , ("(val x e)",                     curry VAL    <$> vvar <*> exp)
      , ("(val-rec x e)",                 curry VALREC <$> vvar <*> exp)
      , ("(data kind t [vcon : type] ...)", data <$> kind <*> tyname <*> many
                                                                            Kty)
      ]
  end
(* type declarations for consistency checking *)
val _ = op def : def parser
(* parsers and [[xdef]] streams for \uml S317a *)
val testtable = usageParsers
  [ ("(check-expect e1 e2)",          curry CHECK_EXPECT     <$> exp <*> exp)
  , ("(check-assert e)",                    CHECK_ASSERT     <$> exp)
  , ("(check-error e)",                     CHECK_ERROR      <$> exp)
  , ("(check-type e tau)",            curry CHECK_TYPE       <$> exp <*> tyex)
  , ("(check-principal-type e tau)",  curry CHECK_PTYPE      <$> exp <*> tyex)
  , ("(check-type-error e)",                CHECK_TYPE_ERROR <$> (def <|>
                                                                    implicitData
                                                                 <|> EXP <$> exp
                                                                              ))
  ]
(* type declarations for consistency checking *)
val _ = op testtable : unit_test parser
(* parsers and [[xdef]] streams for \uml S317b *)
val xdeftable = usageParsers
  [ ("(use filename)", USE <$> any_name)
  (* rows added to \uml's [[xdeftable]] in exercises ((prototype)) S318g *)
  (* you can add a row for 'val' here *)
  (* rows added to \uml's [[xdeftable]] in exercises S319e *)
  (* you add this bit *)
  ]
(* type declarations for consistency checking *)
val _ = op xdeftable : xdef parser
(* parsers and [[xdef]] streams for \uml S317d *)
val xdef  =  TEST <$> testtable
         <|>          xdeftable
         <|> DEF  <$> (def <|> implicitData)
         <|> badRight "unexpected right bracket"
         <|> DEF <$> EXP <$> exp
         <?> "definition"
val xdefstream = interactiveParsedStream (schemeToken, xdef)
(* type declarations for consistency checking *)
val _ = op xdef : xdef parser
(* parsers and [[xdef]] streams for \uml S319b *)
local
  fun sxb b = CONVAL ("Sx.B", [embedBool b])
  fun sxs s = CONVAL ("Sx.S", [SYM s])
  fun sxn n = CONVAL ("Sx.N", [NUM n])
  fun sxlist sxs = CONVAL("Sx.L", [embedList sxs])

  fun sexp tokens = (
         sxb <$> booltok
     <|> sxs <$> (notDot <$>! @@ any_name)
     <|> sxn <$> int
     <|> leftCurly <!> "curly brackets may not be used in S-expressions"
     <|> (fn v => sxlist [sxs "quote", v]) <$> (quote *> sexp)
     <|> sxlist <$> bracket ("list of S-expressions", many sexp)
    ) tokens
  val sexp = sexp <?> "S-expression"
in
  val sxstream = interactiveParsedStream (schemeToken, sexp)
end
(* type declarations for consistency checking *)
val _ = op sxstream : string * line stream * prompts -> value stream
(* shared definitions of [[filexdefs]] and [[stringsxdefs]] S94c *)
fun filexdefs (filename, fd, prompts) = xdefstream (filename, filelines fd,
                                                                        prompts)
fun stringsxdefs (name, strings) = xdefstream (name, streamOfList strings,
                                                                      noPrompts)
(* type declarations for consistency checking *)
val _ = op xdefstream   : string * line stream     * prompts -> xdef stream
val _ = op filexdefs    : string * TextIO.instream * prompts -> xdef stream
val _ = op stringsxdefs : string * string list               -> xdef stream



(*****************************************************************)
(*                                                               *)
(*   DEFINITION OF [[BASIS]] FOR \UML                            *)
(*                                                               *)
(*****************************************************************)

(* definition of [[basis]] for \uml S303f *)
type basis = type_env * (ty * kind) env * value env


(*****************************************************************)
(*                                                               *)
(*   TRANSLATION OF {\UML} TYPE SYNTAX INTO TYPES                *)
(*                                                               *)
(*****************************************************************)

(* translation of {\uml} type syntax into types ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
local
  val known_vcons = ref [] : (tycon * (vcon * type_scheme) list) list ref
in
  fun vconsOf mu =
    case List.find (fn (mu', _) => eqTycon (mu, mu')) (!known_vcons)
      of SOME (_, vcons) => vcons
       | NONE => raise BugInTypeInference "missing vcons"

  fun addVcons (mu, vcons) =
    known_vcons := (mu, vcons) :: !known_vcons
end
(* translation of {\uml} type syntax into types S299b *)
fun txType (TYNAME t, Delta) =
      (find (t, Delta)
       handle NotFound _ => raise TypeError ("unknown type name " ^ t))
  | txType (TYVARX a, Delta) =
      (find (a, Delta)
       handle NotFound _ => raise TypeError ("type variable " ^ a ^
                                                            " is not in scope"))
(* translation of {\uml} type syntax into types S300 *)
  | txType (CONAPPX (tx, txs), Delta) =
      let val (tau,  kind)  = txType (tx, Delta)
          val (taus, kinds) = ListPair.unzip (map (fn tx => txType (tx, Delta))
                                                                            txs)
      in  case kind
            of ARROW (argks, resultk) =>
                 if eqKinds (kinds, argks) then
                   (CONAPP (tau, taus), resultk)
                 else

                  (* applied type constructor [[tx]] has the wrong kind S332b *)
                   if length argks <> length kinds then
                     raise TypeError ("type constructor " ^ typeString tau ^
                                                              " is expecting " ^
                                      countString argks "argument" ^
                                                                  ", but got " ^
                                      Int.toString (length taus))
                   else
                     let fun findBad n (k::ks) (k'::ks') =
                               if eqKind (k, k') then
                                 findBad (n+1) ks ks'
                               else
                                 raise TypeError ("argument " ^ Int.toString n ^
                                                       " to type constructor " ^
                                                  typeString tau ^
                                           " should have kind " ^ kindString k ^
                                                  ", but it has kind " ^
                                                                  kindString k')
                           | findBad _ _ _ = raise InternalError
                                                    "undetected length mismatch"
                     in  findBad 1 argks kinds
                     end
             | TYPE =>
                   (* type [[tau]] is not expecting any arguments S332c *)
                   raise TypeError ("type " ^ typeString tau ^
                                         " is not a type constructor, but it " ^
                                    "was applied to " ^ countString taus
                                                                   "other type")
      end
(* translation of {\uml} type syntax into types S301a *)
  | txType (FUNTYX (txs, tx), Delta) =
      let val tks = map (fn tx => txType (tx, Delta)) txs
          val tk  = txType (tx, Delta)
          fun notAType (ty, kind) = not (eqKind (kind, TYPE))
          fun thetype  (ty, kind) = ty
      in  if notAType tk then
            raise TypeError ("in result position, " ^ typeString (thetype tk) ^
                             " is not a type")
          else
            case List.find notAType tks
              of SOME tk =>
                   raise TypeError ("in argument position, " ^
                                    typeString (thetype tk) ^ " is not a type")
               | NONE => (funtype (map thetype tks, thetype tk), TYPE)
      end
(* translation of {\uml} type syntax into types S301b *)
  | txType (FORALLX _, _) =
      raise TypeError ("'forall' is permissible only at top level")
(* type declarations for consistency checking *)
val _ = op txType : tyex * (ty * kind) env -> ty * kind
(* translation of {\uml} type syntax into types S301c *)
fun txTyScheme (FORALLX (alphas, tx), Delta) =
      let val Delta'   = extend (Delta, map (fn a => (a, (TYVAR a, TYPE)))
                                                                         alphas)
          val (tau, kind) = txType (tx, Delta')
      in  if eqKind (kind, TYPE) then
            FORALL (alphas, tau)
          else
            raise TypeError ("in " ^ typeSchemeString (FORALL (alphas, tau)) ^
                             ", type " ^ typeString tau ^ " has kind " ^
                                                                kindString kind)
      end
(* translation of {\uml} type syntax into types S302a *)
  | txTyScheme (tx, Delta) =
      case txType (tx, Delta)
        of (tau, TYPE) => FORALL ([], tau)
         | (tau, kind) =>
             raise TypeError ("expected a type, but got type constructor " ^
                              typeString tau ^ " of kind " ^ kindString kind)
(* type declarations for consistency checking *)
val _ = op txTyScheme : tyex * (ty * kind) env -> type_scheme


(*****************************************************************)
(*                                                               *)
(*   ELABORATION AND EVALUATION OF [[DATA]] DEFINITIONS          *)
(*                                                               *)
(*****************************************************************)

(* elaboration and evaluation of [[data]] definitions 541 *)
fun elabDataDef ((T, kind, vcons), Gamma, Delta) =
  let
(* definition of [[validate]], for the types of the value constructors of [[T]] S297 *)
      fun validate (K, sigma as FORALL (alphas, _), mu, kind) =
        let
          (* definitions of [[appliesMu]] and [[validateTypeArguments]] S329e *)
            fun appliesMu (CONAPP (tau, _)) = eqType (tau, TYCON mu) 
              | appliesMu _ = false

          (* definitions of [[appliesMu]] and [[validateTypeArguments]] S330a *)
            fun validateTypeArguments (CONAPP (_, taus)) =
                  let fun asTyvar (TYVAR a) = a
                        | asTyvar tau =
                            raise TypeError ("in type of " ^ K ^
                                                           ", type parameter " ^
                                             typeString tau ^ " passed to " ^ T
                                                                               ^
                                             " is not a type variable")
                  in  case duplicatename (map asTyvar taus)
                        of NONE => ()
                         | SOME a => 
                             raise TypeError ("in type of " ^ K ^
                                                   ", type parameters to " ^ T ^
                                              " must be distinct, but " ^ a ^
                                              " is passed to " ^ T ^
                                                              " more than once")
                  end
              | validateTypeArguments (TYCON _) =
                  ()  (* happens only when uML is extended with existentials *)
              | validateTypeArguments _ =
                  let exception ImpossibleTypeArguments in raise
                                                     ImpossibleTypeArguments end
            val desiredType = case kind of TYPE => "type " ^ tyconString mu
                                      | ARROW _ => "a type made with " ^
                                                                  tyconString mu
            fun validateLengths (alphas, argkinds) =
              if length alphas <> length argkinds then

   (* for [[K]], complain that [[alphas]] is inconsistent with [[kind]] S330b *)
                (case kind
                   of TYPE =>
                        raise TypeError ("datatype " ^ T ^
                                              " takes no type parameters, so " ^
                                         "value constructor " ^ K ^
                                                     " must not be polymorphic")
                    | ARROW (kinds, _) => 
                          raise TypeError ("datatype constructor " ^ T ^
                                                                   " expects " ^
                                           intString (length kinds) ^
                                                             " type parameter" ^
                                           (case kinds of [_] => "" | _ => "s")
                                                                               ^
                                           ", but value constructor " ^ K ^
                                           (if null alphas then
                                                           " is not polymorphic"
                                            else " expects " ^ Int.toString (
                                                                length alphas) ^
                                                 " type parameter" ^
                                                 (case alphas of [_] => "" | _
                                                                      => "s"))))
              else
                ()
      (* type declarations for consistency checking *)
      val _ = op appliesMu             : ty -> bool
      val _ = op validateTypeArguments : ty -> unit
      val _ = op validateLengths       : tyvar list * kind list -> unit
        in
   (* validation by case analysis on [[schemeShape shape]] and [[kind]] S298a *)
            case (schemeShape sigma, kind)
              of (MONO_VAL tau, TYPE) =>
                   if eqType (tau, TYCON mu) then
                     ()
                   else

            (* type of [[K]] should be [[desiredType]] but is [[sigma]] S330c *)
                     raise TypeError ("value constructor " ^ K ^ " should have "
                                                                 ^ desiredType ^
                                      ", but it has type " ^ typeSchemeString
                                                                          sigma)
               | (MONO_FUN (_, result), TYPE) =>
                   if eqType (result, TYCON mu) then
                     ()
                   else

    (* result type of [[K]] should be [[desiredType]] but is [[result]] S330d *)
                     raise TypeError ("value constructor " ^ K ^
                                               " should return " ^ desiredType ^
                                      ", but it returns type " ^ typeString
                                                                         result)
               | (POLY_VAL (alphas, tau), ARROW (argkinds, _)) => 
                   if appliesMu tau then
                     ( validateLengths (alphas, argkinds)
                     ; validateTypeArguments tau
                     )
                   else

            (* type of [[K]] should be [[desiredType]] but is [[sigma]] S330c *)
                     raise TypeError ("value constructor " ^ K ^ " should have "
                                                                 ^ desiredType ^
                                      ", but it has type " ^ typeSchemeString
                                                                          sigma)
               | (POLY_FUN (alphas, _, result), ARROW (argkinds, _)) => 
                   if appliesMu result then
                     ( validateLengths (alphas, argkinds)
                     ; validateTypeArguments result
                     )
                   else

    (* result type of [[K]] should be [[desiredType]] but is [[result]] S330d *)
                     raise TypeError ("value constructor " ^ K ^
                                               " should return " ^ desiredType ^
                                      ", but it returns type " ^ typeString
                                                                         result)
               | _ =>

   (* for [[K]], complain that [[alphas]] is inconsistent with [[kind]] S330b *)
                   (case kind
                      of TYPE =>
                           raise TypeError ("datatype " ^ T ^
                                              " takes no type parameters, so " ^
                                            "value constructor " ^ K ^
                                                     " must not be polymorphic")
                       | ARROW (kinds, _) => 
                             raise TypeError ("datatype constructor " ^ T ^
                                                                   " expects " ^
                                              intString (length kinds) ^
                                                             " type parameter" ^
                                              (case kinds of [_] => "" | _ =>
                                                                          "s") ^
                                              ", but value constructor " ^ K ^
                                              (if null alphas then
                                                           " is not polymorphic"
                                               else " expects " ^ Int.toString (
                                                                length alphas) ^
                                                    " type parameter" ^
                                                    (case alphas of [_] => "" |
                                                                    _ => "s"))))
        end                   
      val mu      = freshTycon T
      val Delta'  = bind (T, (TYCON mu, kind), Delta)
      fun translateVcon (K, tx) = (K, txTyScheme (tx, Delta'))
            handle TypeError msg =>
                                                                        (*OMIT*)
              raise TypeError ("in type of value constructor " ^ K ^ ", " ^ msg)
                                                                        (*OMIT*)
      val Ksigmas = map translateVcon vcons
      val ()      = app (fn (K, sigma) => validate (K, sigma, mu, kind)) Ksigmas
      val ()      = addVcons (mu, Ksigmas) (* OMIT *)
      val Gamma'  = extendTypeEnv (Gamma, Ksigmas)
  in  (Gamma', Delta', kindString kind :: map (typeSchemeString o snd) Ksigmas)
  end
(* type declarations for consistency checking *)
val _ = op elabDataDef : data_def * type_env * (ty * kind) env -> type_env * (ty
                                                       * kind) env * string list
(* elaboration and evaluation of [[data]] definitions 542 *)
fun evalDataDef ((_, _, typed_vcons), rho) =
  let fun primFor (K, t) = if isfuntype t then
                             PRIMITIVE (fn vs => CONVAL (K, vs))
                           else
                             CONVAL (K, [])
      fun addVcon ((K, t), rho) = bind (K, primFor (K, t), rho)
(* type declarations for consistency checking *)
val _ = op evalDataDef : data_def * value env -> value env * string list
val _ = op isfuntype   : tyex -> bool
  in  (foldl addVcon rho typed_vcons, map fst typed_vcons)
  end
(* elaboration and evaluation of [[data]] definitions S304b *)
fun processDataDef (dd, (Gamma, Delta, rho), interactivity) =
  let val (Gamma', Delta', tystrings) = elabDataDef (dd, Gamma, Delta)
      val (rho', vcons)               = evalDataDef (dd, rho)
      val _ = if prints interactivity then

               (* print the new type and each of its value constructors S304c *)
                let val (T, _, _) = dd
                    val (mu, _)   = find (T, Delta')
                    val (kind, vcon_types) =
                      case tystrings of s :: ss => (s, ss)
                                      | [] => let exception NoKindString in
                                                          raise NoKindString end
                in  ( println (typeString mu ^ " :: " ^ kind)
                    ; ListPair.appEq (fn (K, tau) => println (K ^ " : " ^ tau))
                                                             (vcons, vcon_types)
                    )
                end
              else
                ()
  in  (Gamma', Delta', rho')
  end
(* type declarations for consistency checking *)
val _ = op processDataDef : data_def * basis * interactivity -> basis


(*****************************************************************)
(*                                                               *)
(*   DEFINITIONS OF [[EMPTYBASIS]], [[PREDEFINEDTYPEBASIS]], [[BOOLTYPE]], [[LISTTYPE]], AND [[UNITTYPE]] *)
(*                                                               *)
(*****************************************************************)

(* definitions of [[emptyBasis]], [[predefinedTypeBasis]], [[booltype]], [[listtype]], and [[unittype]] S305a *)
val emptyBasis = (emptyTypeEnv, emptyEnv, emptyEnv)
fun addTycon ((t, tycon, kind), (Gamma, Delta, rho)) =
  (Gamma, bind (t, (TYCON tycon, kind), Delta), rho)
val primTyconBasis : basis = 
  foldl addTycon emptyBasis (
                        (* primitive type constructors for \uml\ [[::]] S306d *)
                             ("int", inttycon, TYPE) :: 
                             ("sym", symtycon, TYPE) :: nil)
(* definitions of [[emptyBasis]], [[predefinedTypeBasis]], [[booltype]], [[listtype]], and [[unittype]] S305b *)
val predefinedTypeBasis =
  let val predefinedTypes = 
                             [ ";  predefined uML types 513d "
                             , "(data (* => *) option"
                             , "  [SOME : (forall ('a) ('a -> (option 'a)))]"
                             , "  [NONE : (forall ('a) (option 'a))])"
                             , ";  predefined uML types 524 "
                             , "(data * bool"
                             , "  [#t : bool]"
                             , "  [#f : bool])"
                             , ";  predefined uML types 525a "
                             , "(data (* => *) list"
                             , "  ['()  : (forall ('a) (list 'a))]"
                             ,
                         "  [cons : (forall ('a) ('a (list 'a) -> (list 'a)))])"
                             , ";  predefined uML types 525b "
                             , "(data * unit [UNIT : unit])"
                             , ";  predefined uML types 525c "
                             , "(implicit-data order LESS EQUAL GREATER)"
                             , ";  predefined uML types S293b "
                             , "(data (* * * => *) triple"
                             ,
             "  [TRIPLE : (forall ('a 'b 'c) ('a 'b 'c -> (triple 'a 'b 'c)))])"
                             , ";  predefined uML types S293c "
                             , "(implicit-data ('a1 'a2 'a3 'a4) 4-tuple"
                             , "         [T4 of 'a1 'a2 'a3 'a4])"
                             , "(implicit-data ('a1 'a2 'a3 'a4 'a5) 5-tuple"
                             , "         [T5 of 'a1 'a2 'a3 'a4 'a5])"
                             ,
                              "(implicit-data ('a1 'a2 'a3 'a4 'a5 'a6) 6-tuple"
                             , "         [T6 of 'a1 'a2 'a3 'a4 'a5 'a6])"
                             ,
                          "(implicit-data ('a1 'a2 'a3 'a4 'a5 'a6 'a7) 7-tuple"
                             , "         [T7 of 'a1 'a2 'a3 'a4 'a5 'a6 'a7])"
                             ,
                      "(implicit-data ('a1 'a2 'a3 'a4 'a5 'a6 'a7 'a8) 8-tuple"
                             ,
                             "         [T8 of 'a1 'a2 'a3 'a4 'a5 'a6 'a7 'a8])"
                             ,
                  "(implicit-data ('a1 'a2 'a3 'a4 'a5 'a6 'a7 'a8 'a9) 9-tuple"
                             ,
                         "         [T9 of 'a1 'a2 'a3 'a4 'a5 'a6 'a7 'a8 'a9])"
                             ,
            "(implicit-data ('a1 'a2 'a3 'a4 'a5 'a6 'a7 'a8 'a9 'a10) 10-tuple"
                             ,
                    "        [T10 of 'a1 'a2 'a3 'a4 'a5 'a6 'a7 'a8 'a9 'a10])"
                             , ";  predefined uML types S319a "
                             , "(data * sx"
                             , "   [Sx.B : (bool -> sx)]"
                             , "   [Sx.S : (sym  -> sx)]"
                             , "   [Sx.N : (int  -> sx)]"
                             , "   [Sx.L : ((list sx)  -> sx)])"
                              ] 
      val xdefs = stringsxdefs ("built-in types", predefinedTypes)
      fun process (DEF (DATA dd), b) = processDataDef (dd, b, noninteractive)
        | process _ = raise InternalError "predefined definition is not DATA"
  in  streamFold process primTyconBasis xdefs
  end
(* type declarations for consistency checking *)
val _ = op emptyBasis : basis
(* type declarations for consistency checking *)
val _ = op predefinedTypeBasis : basis
(* definitions of [[emptyBasis]], [[predefinedTypeBasis]], [[booltype]], [[listtype]], and [[unittype]] S306c *)
local
  val (_, Delta, _) = predefinedTypeBasis
  fun predefined t = fst (find (t, Delta))
  val listtycon = predefined "list"
in
  val booltype     = predefined "bool"
  fun listtype tau = CONAPP (listtycon, [tau])
  val unittype     = predefined "unit"
  val sxtype       = predefined "sx"
  val alpha = TYVAR "'a"
  val beta  = TYVAR "'b"
end


(*****************************************************************)
(*                                                               *)
(*   TYPE INFERENCE FOR \NML\ AND \UML                           *)
(*                                                               *)
(*****************************************************************)

(* type inference for \nml\ and \uml S263d *)
(* representation of type constraints 485e *)
datatype con = ~  of ty  * ty
             | /\ of con * con
             | TRIVIAL
infix 4 ~
infix 3 /\
(* utility functions on type constraints 486a *)
fun freetyvarsConstraint (t ~  t') = union (freetyvars t, freetyvars t')
  | freetyvarsConstraint (c /\ c') = union (freetyvarsConstraint c,
                                             freetyvarsConstraint c')
  | freetyvarsConstraint TRIVIAL    = emptyset
(* utility functions on type constraints 486b *)
fun consubst theta =
  let fun subst (tau1 ~ tau2) = tysubst theta tau1 ~ tysubst theta tau2
        | subst (c1 /\ c2)    = subst c1 /\ subst c2
        | subst TRIVIAL       = TRIVIAL
  in  subst
  end
(* type declarations for consistency checking *)
val _ = op bindtyscheme : name * type_scheme * type_env -> type_env
(* type declarations for consistency checking *)
val _ = op freetyvarsGamma : type_env -> name set
(* type declarations for consistency checking *)
val _ = op consubst : subst -> con -> con
(* utility functions on type constraints 486c *)
fun conjoinConstraints []      = TRIVIAL
  | conjoinConstraints [c]     = c
  | conjoinConstraints (c::cs) = c /\ conjoinConstraints cs
(* type declarations for consistency checking *)
val _ = op conjoinConstraints : con list -> con
(* utility functions on type constraints 487b *)
fun isSolved TRIVIAL = true
  | isSolved (tau ~ tau') = eqType (tau, tau')
  | isSolved (c /\ c') = isSolved c andalso isSolved c'
fun solves (theta, c) = isSolved (consubst theta c)
(* type declarations for consistency checking *)
val _ = op isSolved : con -> bool
val _ = op solves : subst * con -> bool
(* utility functions on type constraints S263c *)
(* definitions of [[constraintString]] and [[untriviate]] S270c *)
fun constraintString (c /\ c') = constraintString c ^ " /\\ " ^ constraintString
                                                                              c'
  | constraintString (t ~  t') = typeString t ^ " ~ " ^ typeString t'
  | constraintString TRIVIAL = "TRIVIAL"

fun untriviate (c /\ c') = (case (untriviate c, untriviate c')
                              of (TRIVIAL, c) => c
                               | (c, TRIVIAL) => c
                               | (c, c') => c /\ c')
  | untriviate atomic = atomic
(* type declarations for consistency checking *)
val _ = op constraintString : con -> string
val _ = op untriviate       : con -> con
(* constraint solving 486d *)
fun unsatisfiableEquality (t1, t2) =
  let val t1_arrow_t2 = funtype ([t1], t2)
      val FORALL (_, canonical) =
            canonicalize (FORALL (freetyvars t1_arrow_t2, t1_arrow_t2))
  in  case asFuntype canonical
        of SOME ([t1'], t2') =>
             raise TypeError ("cannot make " ^ typeString t1' ^
                              " equal to " ^ typeString t2')
         | _ => let exception ThisCan'tHappen in raise ThisCan'tHappen end
  end
(* constraint solving ((prototype)) 487a *)
fun solve c = raise LeftAsExercise "solve"
(* type declarations for consistency checking *)
val _ = op solve : con -> subst
(* constraint solving ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
fun hasNoSolution c = (solve c; false) handle TypeError _ => true
fun hasGoodSolution c = solves (solve c, c) handle TypeError _ => false
val hasSolution = not o hasNoSolution
fun solutionEquivalentTo (c, theta) = eqsubst (solve c, theta)

fun assert p = if p then () else let exception Assert in raise Assert end

val () = assert (hasNoSolution (inttype ~ booltype))
val () = assert (hasSolution (booltype ~ booltype))


val () = assert (solutionEquivalentTo (booltype ~ TYVAR "a", "a" |--> booltype))

(* exhaustiveness analysis for {\uml} 593a *)
datatype simple_vset = ALL of ty
                     | ONE of vcon * simple_vset list
type vset = simple_vset collection
(* exhaustiveness analysis for {\uml} ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
fun vsetString (ALL tau) = "_" (* (ALL : " ^ typeString tau ^ ")" *)
  | vsetString (ONE (K, [])) = K
  | vsetString (ONE (K, vsets)) = "(" ^ K ^ " " ^ spaceSep (map vsetString vsets
                                                                         ) ^ ")"
(* exhaustiveness analysis for {\uml} ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
fun hasAll (ALL _) = true
  | hasAll (ONE (_, vs)) = List.exists hasAll vs
(* exhaustiveness analysis for {\uml} ((prototype)) 593b *)
fun classifyVset   p vs = joinC (mapC (classifySimple p) vs)
and classifySimple p vs = raise LeftAsExercise "pattern-matching classification"
(* exhaustiveness analysis for {\uml} 594a *)
fun unroll tau =
  let val mu = case tau of TYCON mu => mu
                         | CONAPP (TYCON mu, _) => mu
                         | _ => raise BugInTypeInference "not ADT"
      fun ofVcon (name, sigma) =
        let val tau'   = freshInstance sigma
            val argTys = case asFuntype tau'
                           of SOME (args, res) =>
                                let val theta = solve (res ~ tau)
                                in  map (tysubst theta) args
                                end
                            | NONE => []
        in  ONE (name, map ALL argTys) : simple_vset
        end
  in  C (map ofVcon (vconsOf mu))
  end
(* exhaustiveness analysis for {\uml} ((prototype)) 594b *)
fun exhaustivenessCheck (ps, tau) =
  eprintln "(Case expression not checked for exhaustiveness.)"
(* exhaustiveness analysis for {\uml} S278g *)
(* filled in when implementing uML *)
(* definitions of [[typeof]] and [[elabdef]] for \nml\ and \uml 487c *)
fun typeof (e, Gamma) =
  let
(* shared definition of [[typesof]], to infer the types of a list of expressions 487d *)
      fun typesof ([],    Gamma) = ([], TRIVIAL)
        | typesof (e::es, Gamma) =
            let val (tau,  c)  = typeof  (e,  Gamma)
                val (taus, c') = typesof (es, Gamma)
            in  (tau :: taus, c /\ c')
            end

(* function [[literal]], to infer the type of a literal constant ((prototype)) 488b *)
      fun literal _ = raise LeftAsExercise "literal"

(* function [[literal]], to infer the type of a literal constant ((adt)) S303b *)
      (* definition of function [[pvconType]] S303d *)
      fun pvconType (K, Gamma) =
        freshInstance (findtyscheme (K, Gamma))
        handle NotFound x => raise TypeError ("no value constructor named " ^ x)
      (* definition of function [[pattype]] 550 *)
      fun pattype(p as CONPAT (vcon, pats as _ :: _), Gamma) = 
            let val vcon_tau = pvconType (vcon, Gamma)
                val (Gamma'_is, tau_is, c_is) = pattypes (pats, Gamma)
                val alpha  = freshtyvar ()
                val c      = vcon_tau ~ funtype (tau_is, alpha)
                val c'     = conjoinConstraints c_is
                val Gamma' = disjointUnion Gamma'_is
                             handle DisjointUnionFailed x =>
                               raise TypeError ("name " ^ x ^
                                                         " is bound multiple " ^
                                                "times in pattern " ^ patString
                                                                              p)
            in  (Gamma', alpha, c /\ c')
            end
        | pattype (CONPAT (K, []), Gamma) =
            (emptyEnv, pvconType (K, Gamma), TRIVIAL)
        | pattype (WILDCARD, _) =
            (emptyEnv, freshtyvar(), TRIVIAL)
        | pattype (PVAR x, _) =
            let val alpha = freshtyvar ()
      (* type declarations for consistency checking *)
            in  (bind (x, FORALL ([], alpha), emptyEnv), alpha, TRIVIAL)
            end
      and pattypes (ps, Gamma) = unzip3 (map (fn p => pattype (p, Gamma)) ps)
      (* definition of function [[choicetype]] 549b *)
      fun choicetype ((p, e), Gamma) =
            let val (Gamma', tau, c) = pattype (p, Gamma)
                val (tau', c') = typeof (e, extendTypeEnv (Gamma, Gamma'))
                val (ty, con) = (funtype ([tau], tau'), c /\ c')
                val _ =
(* check [[p]], [[e]], [[Gamma']], [[Gamma]], [[ty]], and [[con]] for escaping skolem types S311d *)
                        ()          
      (* type declarations for consistency checking *)
      val _ = op choicetype : (pat * exp) * type_env -> ty * con
            in  (ty, con)
            end

(* function [[ty]], to infer the type of a \nml\ expression, given [[Gamma]] 488a *)
      fun ty (LITERAL n) = literal n
        | ty (VAR x) = (freshInstance (findtyscheme (x, Gamma)), TRIVIAL)
        (* more alternatives for [[ty]] 488c *)
        | ty (APPLY (f, actuals)) = 
             (case typesof (f :: actuals, Gamma)
                of ([], _) => let exception ThisCan'tHappen in raise
                                                             ThisCan'tHappen end
                 | (funty :: actualtypes, c) =>
                      let val rettype = freshtyvar ()
                      in  (rettype, c /\ (funty ~ funtype (actualtypes, rettype)
                                                                              ))
                      end)
        (* more alternatives for [[ty]] 488d *)
        | ty (LETX (LETSTAR, [], body)) = ty body
        | ty (LETX (LETSTAR, (b :: bs), body)) = 
            ty (LETX (LET, [b], LETX (LETSTAR, bs, body)))
        (* more alternatives for [[ty]] ((prototype)) 488e *)
        | ty (IFX (e1, e2, e3))        = raise LeftAsExercise "type for IFX"
        | ty (BEGIN es)                = raise LeftAsExercise "type for BEGIN"
        | ty (LAMBDA (formals, body))  = raise LeftAsExercise "type for LAMBDA"
        | ty (LETX (LET, bs, body))    = raise LeftAsExercise "type for LET"
        | ty (LETX (LETREC, bs, body)) = raise LeftAsExercise "type for LETREC"
        (* more alternatives for [[ty]] 549a *)
        | ty (CASE (e, choices)) = 
            let val (tau, c_e) =
                      typeof (e, Gamma)
                val (tau_i's, c_i's) =
                      ListPair.unzip (map (fn choice => choicetype (choice,
                                                                Gamma)) choices)
                val alpha = freshtyvar ()
                fun constrainArrow tau_i = tau_i ~ funtype ([tau], alpha)
                val c' = conjoinConstraints (map constrainArrow tau_i's)
                val c = c_e /\ c' /\ conjoinConstraints c_i's
                val () = exhaustivenessCheck (map fst choices, tysubst (solve c)
                                                                 tau) (* OMIT *)
        (* type declarations for consistency checking *)
        val _ = op ty         : exp                    -> ty * con
        val _ = op typeof     : exp         * type_env -> ty * con
        val _ = op choicetype : (pat * exp) * type_env -> ty * con
            in  (alpha, c)
            end
        (* more alternatives for [[ty]] S303e *)
        | ty (VCONX vcon) =
            let val tau =
                  freshInstance (findtyscheme (vcon, Gamma))
                  handle NotFound _ => raise TypeError (
                                           "no value constructor named " ^ vcon)
            in  (tau, TRIVIAL)
            end
(* type declarations for consistency checking *)
val _ = op typeof  : exp      * type_env -> ty      * con
val _ = op typesof : exp list * type_env -> ty list * con
val _ = op literal : value -> ty * con
val _ = op ty      : exp   -> ty * con
  in  ty e
  end
(* definitions of [[typeof]] and [[elabdef]] for \nml\ and \uml 489a *)
fun elabdef (d, Gamma) =
  case d
    of VAL    (x, e)      =>
                   (* infer and bind type for [[VAL    (x, e)]] for \nml 489b *)
                             let val (tau, c) = typeof (e, Gamma)
                                 val theta    = solve c
                                 val sigma    = generalize (tysubst theta tau,
                                                          freetyvarsGamma Gamma)
                             in  (bindtyscheme (x, sigma, Gamma),
                                                         typeSchemeString sigma)
                             end
     | VALREC (x, e)      =>
                   (* infer and bind type for [[VALREC (x, e)]] for \nml 489c *)
                             let val alpha    = freshtyvar ()
                                 val Gamma'   = bindtyscheme (x, FORALL ([],
                                                                  alpha), Gamma)
                                 val (tau, c) = typeof (e, Gamma')
                                 val theta    = solve (c /\ alpha ~ tau)
                                 val sigma    = generalize (tysubst theta alpha,
                                                          freetyvarsGamma Gamma)
                             in  (bindtyscheme (x, sigma, Gamma),
                                                         typeSchemeString sigma)
                             end
     | EXP e              => elabdef (VAL ("it", e), Gamma)
     | DEFINE (x, lambda) => elabdef (VALREC (x, LAMBDA lambda), Gamma)
     (* extra case for [[elabdef]] used only in \uml S329c *)
     | DATA _ => raise InternalError "DATA reached elabdef"
     (* extra case for [[elabdef]] used only in \uml S278f *)
     (* filled in when implementing uML *)
(* type declarations for consistency checking *)
val _ = op elabdef : def * type_env -> type_env * string
(* type declarations for consistency checking *)
val _ = op typeof  : exp * type_env -> ty * con
val _ = op elabdef : def * type_env -> type_env * string



(*****************************************************************)
(*                                                               *)
(*   EVALUATION, TESTING, AND THE READ-EVAL-PRINT LOOP FOR \UML  *)
(*                                                               *)
(*****************************************************************)

(* evaluation, testing, and the read-eval-print loop for \uml S302b *)
(* definition of [[namedValueString]] for functional bridge languages S258a *)
fun namedValueString x v =
  case v of CLOSURE _ => x
          | PRIMITIVE _ => x
          | _ => valueString v
(* type declarations for consistency checking *)
val _ = op namedValueString : name -> value -> string
(* definitions of [[match]] and [[Doesn'tMatch]] 546 *)
exception Doesn'tMatch    (* pattern-match failure *)
fun match (CONPAT (k, ps), CONVAL (k', vs)) =
     if k = k' then
       disjointUnion (ListPair.mapEq match (ps, vs))
     else
       raise Doesn'tMatch
  | match (CONPAT _, _) = raise Doesn'tMatch
  | match (WILDCARD, _) = emptyEnv
  | match (PVAR x,   v) = bind (x, v, emptyEnv)
(* type declarations for consistency checking *)
val _ = op match         : pat * value -> value env (* or raises Doesn'tMatch *)
val _ = op disjointUnion : 'a env list -> 'a env
(* definitions of [[eval]] and [[evaldef]] for \nml\ and \uml S264b *)
fun eval (e, rho) =
  let val go = applyCheckingOverflow id in go end (* OMIT *)
  let fun ev (LITERAL v)        = v
        | ev (VAR x)            = find (x, rho)
        | ev (IFX (e1, e2, e3)) = ev (if bool (ev e1) then e2 else e3)
        | ev (LAMBDA l)         = CLOSURE (l, fn _ => rho)
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, embedBool false)
            end
        | ev (APPLY (f, args)) = 
           (case ev f
              of PRIMITIVE prim => prim (map ev args)
               | CLOSURE clo =>
                            (* apply closure [[clo]] to [[args]] ((ml)) S264c *)
                                let val ((formals, body), mkRho) = clo
                                    val actuals = map ev args
                                in  eval (body, bindList (formals, actuals,
                                                                      mkRho ()))
                                    handle BindListLength => 
                                        raise BugInTypeInference
                                          "Wrong number of arguments to closure"
                                end
               | _ => raise BugInTypeInference "Applied non-function"
               )
        (* more alternatives for [[ev]] for \nml\ and \uml 543 *)
        | ev (CASE (LITERAL v, (p, e) :: choices)) =
            (let val rho' = match (p, v)
        (* type declarations for consistency checking *)
        val _ = op match  : pat * value -> value env
        val _ = op extend : 'a env * 'a env -> 'a env
             in  eval (e, extend (rho, rho'))
             end
             handle Doesn'tMatch => ev (CASE (LITERAL v, choices)))
        | ev (CASE (LITERAL v, [])) =
            raise RuntimeError ("'case' does not match " ^ valueString v)
        | ev (CASE (e, choices)) =
            ev (CASE (LITERAL (ev e), choices))
        (* more alternatives for [[ev]] for \nml\ and \uml S302c *)
        | ev (VCONX vcon) = find (vcon, rho)
        (* more alternatives for [[ev]] for \nml\ and \uml S265a *)
        | ev (LETX (LET, bs, body)) =
            let val (names, values) = ListPair.unzip bs
            in  eval (body, bindList (names, map ev values, rho))
            end
        (* more alternatives for [[ev]] for \nml\ and \uml S265b *)
        | ev (LETX (LETSTAR, bs, body)) =
            let fun step ((x, e), rho) = bind (x, eval (e, rho), rho)
            in  eval (body, foldl step rho bs)
            end
        (* more alternatives for [[ev]] for \nml\ and \uml S265c *)
        | ev (LETX (LETREC, bs, body)) =
            let fun makeRho' () =
                  let fun step ((x, e), rho) =
                            (case e
                               of LAMBDA l => bind (x, CLOSURE (l, makeRho'),
                                                                            rho)
                                | _ => raise RuntimeError "non-lambda in letrec"
                                                                               )
                  in  foldl step rho bs
                  end
            in  eval (body, makeRho'())
            end
  in  ev e
  end
(* type declarations for consistency checking *)
val _ = op eval : exp * value env -> value
(* definitions of [[eval]] and [[evaldef]] for \nml\ and \uml S265d *)
fun evaldef (VAL (x, e), rho) =
      let val v   = eval (e, rho)
          val rho = bind (x, v, rho)
      in  (rho, namedValueString x v)
      end
  | evaldef (VALREC (f, LAMBDA lambda), rho) =
      let fun makeRho' () = bind (f, CLOSURE (lambda, makeRho'), rho)
          val v           = CLOSURE (lambda, makeRho')
      in  (makeRho'(), f)
      end
  | evaldef (VALREC _, rho) =
      raise RuntimeError "expression in val-rec must be lambda"
  | evaldef (EXP e, rho) = 
      let val v   = eval (e, rho)
          val rho = bind ("it", v, rho)
      in  (rho, valueString v)
      end
(* definitions of [[eval]] and [[evaldef]] for \nml\ and \uml S266a *)
  | evaldef (DEFINE (f, lambda), rho) =
      evaldef (VALREC (f, LAMBDA lambda), rho)
  (* clause for [[evaldef]] for datatype definition (\uml\ only) S329d *)
  | evaldef (DATA _, _) = raise InternalError "DATA reached evaldef"
  (* clause for [[evaldef]] for datatype definition (\uml\ only) S266b *)
  (* code goes here in Chapter 11 *)
(* type declarations for consistency checking *)
val _ = op evaldef : def * value env -> value env * string
(* definition of [[processDef]] for \uml S304a *)
fun processDef (DATA dd, basis, interactivity) =
      processDataDef (dd, basis, interactivity)
  | processDef (d, (Gamma, Delta, rho), interactivity) =
      let val (Gamma', tystring)  = elabdef (d, Gamma)
          val (rho',   valstring) = evaldef (d, rho)
          val _ =
            if prints interactivity then
              println (valstring ^ " : " ^ tystring)
            else
              ()
(* type declarations for consistency checking *)
val _ = op processDef : def * basis * interactivity -> basis
      in  (Gamma', Delta, rho')
      end
fun dump_names (_, _, values) = app (println o fst) values  (*OMIT*)
(* shared definition of [[withHandlers]] S223b *)
fun withHandlers f a caught =
  f a
  handle RuntimeError msg   => caught ("Run-time error <at loc>: " ^ msg)
       | NotFound x         => caught ("Name " ^ x ^ " not found <at loc>")
       | Located (loc, exn) =>
           withHandlers (fn _ => raise exn) a (fn s => caught (fillAtLoc (s, loc
                                                                             )))

(* other handlers that catch non-fatal exceptions and pass messages to [[caught]] S224a *)
       | Div                => caught ("Division by zero <at loc>")
       | Overflow           => caught ("Arithmetic overflow <at loc>")
       | Subscript          => caught ("Array index out of bounds <at loc>")
       | Size               => caught (
                                "Array length too large (or negative) <at loc>")
       | IO.Io { name, ...} => caught ("I/O error <at loc>: " ^ name)

(* other handlers that catch non-fatal exceptions and pass messages to [[caught]] ((type-inference)) S269a *)
       | TypeError          msg => caught ("type error <at loc>: " ^ msg)
       | BugInTypeInference msg => caught ("bug in type inference: " ^ msg)
(* shared unit-testing utilities S86d *)
fun failtest strings = (app eprint strings; eprint "\n"; false)
(* shared unit-testing utilities S86e *)
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
(* definition of [[testIsGood]] for \uml S328 *)
(* definition of [[skolemTypes]] for languages with generated type constructors S329b *)
val skolemTypes =
  streamOfEffects (fn () => SOME (TYCON (freshTycon "skolem type")))
(* shared definitions of [[typeSchemeIsAscribable]] and [[typeSchemeIsEquivalent]] S274d *)
fun asGeneralAs (sigma_g, sigma_i as FORALL (a's, tau)) =
  let val theta = bindList (a's, streamTake (length a's, skolemTypes), emptyEnv)
                                                                                
      val skolemized = tysubst theta tau
      val tau_g = freshInstance sigma_g
  in  (solve (tau_g ~ skolemized); true) handle _ => false
  end
(* shared definitions of [[typeSchemeIsAscribable]] and [[typeSchemeIsEquivalent]] S274e *)
fun eqTypeScheme (sigma1, sigma2) =
  asGeneralAs (sigma1, sigma2) andalso asGeneralAs (sigma2, sigma1)
(* type declarations for consistency checking *)
val _ = op xdef : xdef parser
(* type declarations for consistency checking *)
val _ = op skolemTypes  : ty stream
(* type declarations for consistency checking *)
val _ = op asGeneralAs  : type_scheme * type_scheme -> bool
(* shared definitions of [[typeSchemeIsAscribable]] and [[typeSchemeIsEquivalent]] S274f *)
fun typeSchemeIsAscribable (e, sigma_e, sigma) =
  if asGeneralAs (sigma_e, sigma) then
    true
  else
    failtest ["check-type failed: expected ", expString e, " to have type ",
              typeSchemeString sigma, ", but it has type ", typeSchemeString
                                                                        sigma_e]
(* shared definitions of [[typeSchemeIsAscribable]] and [[typeSchemeIsEquivalent]] S275a *)
fun typeSchemeIsEquivalent (e, sigma_e, sigma) =
  if typeSchemeIsAscribable (e, sigma_e, sigma) then
    if asGeneralAs (sigma, sigma_e) then
      true
    else
      failtest ["check-principal-type failed: expected ", expString e,
                " to have principal type ", typeSchemeString sigma,
                ", but it has the more general type ", typeSchemeString sigma_e]
  else
    false  (* error message already issued *)
fun testIsGood (test, (Gamma, Delta, rho)) =
  let fun ty e = typeof (e, Gamma)
                 handle NotFound x => raise TypeError ("name " ^ x ^
                                                              " is not defined")
      fun ddtystring dd =
        case elabDataDef (dd, Gamma, Delta)
          of (_, _, kind :: _) => kind
           | _ => "???"
      fun deftystring d =
        (case d of DATA dd => ddtystring dd
                 | _ => snd (elabdef (d, Gamma)))
        handle NotFound x => raise TypeError ("name " ^ x ^ " is not defined")

(* definitions of [[check{Expect,Assert,Error}Checks]] that use type inference S273b *)
      fun checkExpectChecks (e1, e2) = 
        let val (tau1, c1) = ty e1
            val (tau2, c2) = ty e2
            val c = tau1 ~ tau2
            val theta = solve (c1 /\ c2 /\ c)
        in  true
        end handle TypeError msg =>
            failtest ["In (check-expect ", expString e1, " ", expString e2,
                                                                     "), ", msg]

(* definitions of [[check{Expect,Assert,Error}Checks]] that use type inference S274a *)
      fun checkExpChecksIn what e =
        let val (tau, c) = ty e
            val theta = solve c
        in  true
        end handle TypeError msg =>
            failtest ["In (", what, " ", expString e, "), ", msg]
      val checkAssertChecks = checkExpChecksIn "check-assert"
      val checkErrorChecks  = checkExpChecksIn "check-error"
      (* definition of [[checkTypeChecks]] using type inference S274b *)
      fun checkTypeChecks form (e, sigma) = 
        let val (tau, c) = ty e
            val theta  = solve c
        in  true
        end handle TypeError msg =>
            failtest ["In (", form, " ", expString e, " " ^ typeSchemeString
                                                                   sigma, "), ",
                      msg]

      fun withTranslatedSigma check form (e, sigmax) =
        check (e, txTyScheme (sigmax, Delta))
        handle TypeError msg =>
          failtest ["In (", form, " ", expString e, " ", tyexString sigmax,
                                                                     "), ", msg]

      val checkTxTypeChecks =
        withTranslatedSigma (checkTypeChecks "check-type") "check-type"
      val checkTxPtypeChecks =
        withTranslatedSigma (checkTypeChecks "check-principal-type")
                            "check-principal-type"
             
      fun checks (CHECK_EXPECT (e1, e2))    = checkExpectChecks (e1, e2)
        | checks (CHECK_ASSERT e)           = checkAssertChecks e
        | checks (CHECK_ERROR e)            = checkErrorChecks  e
        | checks (CHECK_TYPE  (e, sigmax))  = checkTxTypeChecks (e, sigmax)
        | checks (CHECK_PTYPE (e, sigmax))  = checkTxPtypeChecks (e, sigmax)
        | checks (CHECK_TYPE_ERROR e)       = true

      fun outcome e = withHandlers (fn () => OK (eval (e, rho))) () (ERROR o
                                                                     stripAtLoc)
      (* [[asSyntacticValue]] for \uml S329a *)
      fun asSyntacticValue (LITERAL v) = SOME v
        | asSyntacticValue (VCONX c)   = SOME (CONVAL (c, []))
        | asSyntacticValue (APPLY (e, es)) =
            (case (asSyntacticValue e, optionList (map asSyntacticValue es))
               of (SOME (CONVAL (c, [])), SOME vs) => SOME (CONVAL (c, vs))
                | _ => NONE)
        | asSyntacticValue _ = NONE
      (* type declarations for consistency checking *)
      val _ = op asSyntacticValue : exp -> value option

  (* shared [[check{Expect,Assert,Error}Passes]], which call [[outcome]] S86c *)
      (* shared [[whatWasExpected]] S84b *)
      fun whatWasExpected (e, outcome) =
        case asSyntacticValue e
          of SOME v => valueString v
           | NONE =>
               case outcome
                 of OK v => valueString v ^ " (from evaluating " ^ expString e ^
                                                                             ")"
                  | ERROR _ =>  "the result of evaluating " ^ expString e
      (* type declarations for consistency checking *)
      val _ = op whatWasExpected  : exp * value error -> string
      val _ = op asSyntacticValue : exp -> value option
      (* shared [[checkExpectPassesWith]], which calls [[outcome]] S85 *)
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
      (* type declarations for consistency checking *)
      val _ = op checkExpectPassesWith : (value * value -> bool) -> exp * exp ->
                                                                            bool
      val _ = op outcome  : exp -> value error
      val _ = op failtest : string list -> bool

(* shared [[checkAssertPasses]] and [[checkErrorPasses]], which call [[outcome]] S86a *)
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
      (* type declarations for consistency checking *)
      val _ = op checkAssertPasses : exp -> bool

(* shared [[checkAssertPasses]] and [[checkErrorPasses]], which call [[outcome]] S86b *)
      val cefailed = "check-error failed: "
      fun checkErrorPasses checkx =
            case outcome checkx
              of ERROR _ => true
               | OK check =>
                   failtest [cefailed, " expected evaluating ", expString checkx
                                                                               ,
                             " to cause an error, but evaluation produced ",
                             valueString check]
      (* type declarations for consistency checking *)
      val _ = op checkErrorPasses : exp -> bool
      fun checkExpectPasses (cx, ex) = checkExpectPassesWith testEqual (cx, ex)
      (* definitions of [[check*Type*Passes]] using type inference S275b *)
      fun checkTypePasses (e, sigma) =
        let val (tau, c) = ty e
            val theta    = solve c
            val sigma_e  = generalize (tysubst theta tau, freetyvarsGamma Gamma)
        in  typeSchemeIsAscribable (e, sigma_e, sigma)
        end handle TypeError msg =>
            failtest ["In (check-type ", expString e, " ", typeSchemeString
                                                              sigma, "), ", msg]
      (* definitions of [[check*Type*Passes]] using type inference S275c *)
      fun checkPrincipalTypePasses (e, sigma) =
        let val (tau, c) = ty e
            val theta    = solve c
            val sigma_e  = generalize (tysubst theta tau, freetyvarsGamma Gamma)
        in  typeSchemeIsEquivalent (e, sigma_e, sigma)
        end handle TypeError msg =>
            failtest ["In (check-principal-type ", expString e, " ",
                      typeSchemeString sigma, "), ", msg]
      (* definitions of [[check*Type*Passes]] using type inference S275d *)
      fun checkTypeErrorPasses (EXP e) =
            (let val (tau, c) = ty e
                 val theta    = solve c
                 val sigma'   = generalize (tysubst theta tau, freetyvarsGamma
                                                                          Gamma)
             in  failtest ["check-type-error failed: expected ", expString e,
                           " not to have a type, but it has type ",
                                                        typeSchemeString sigma']
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

      val checkTxTypePasses =
        withTranslatedSigma checkTypePasses          "check-type"
      val checkTxPtypePasses =
        withTranslatedSigma checkPrincipalTypePasses "check-principal-type"

      fun passes (CHECK_EXPECT (c, e))     = checkExpectPasses    (c, e)
        | passes (CHECK_ASSERT c)          = checkAssertPasses    c
        | passes (CHECK_ERROR c)           = checkErrorPasses     c
        | passes (CHECK_TYPE (c, sigmax))  = checkTxTypePasses    (c, sigmax)
        | passes (CHECK_PTYPE (c, sigmax)) = checkTxPtypePasses   (c, sigmax)
        | passes (CHECK_TYPE_ERROR d)      = checkTypeErrorPasses d

  in  checks test andalso passes test
  end
(* definition of [[testIsGood]] for \uml S333 *)
fun assertPtype (x, t, (Gamma, Delta, _)) = 
  let val sigma_x = findtyscheme (x, Gamma)
      val sigma   = txTyScheme (t, Delta)
      fun fail ss = raise TypeError (concat ss)
  in  if typeSchemeIsEquivalent (VAR x, sigma_x, sigma) then
        ()
      else
        fail [ "In (check-principal-type* ", x, " ", typeSchemeString sigma,
                                                                           "), "
             , x, " has principal type ", typeSchemeString sigma_x]
  end
(* shared definition of [[processTests]] S87a *)
fun numberOfGoodTests (tests, rho) =
  foldr (fn (t, n) => if testIsGood (t, rho) then n + 1 else n) 0 tests
fun processTests (tests, rho) =
      reportTestResults (numberOfGoodTests (tests, rho), length tests)
(* type declarations for consistency checking *)
val _ = op processTests : unit_test list * basis -> unit
(* shared read-eval-print loop and [[processPredefined]] S221a *)
fun processPredefined (def,basis) = 
  processDef (def, basis, noninteractive)
(* type declarations for consistency checking *)
val _ = op noninteractive    : interactivity
val _ = op processPredefined : def * basis -> basis
(* shared read-eval-print loop and [[processPredefined]] S221c *)
fun readEvalPrintWith errmsg (xdefs, basis, interactivity) =
  let val unitTests = ref []

(* definition of [[processXDef]], which can modify [[unitTests]] and call [[errmsg]] S222b *)
      fun processXDef (xd, basis) =
        let (* definition of [[useFile]], to read from a file S222a *)
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
      (* type declarations for consistency checking *)
      val _ = op errmsg     : string -> unit
      val _ = op processDef : def * basis * interactivity -> basis
      val basis = streamFold processXDef basis xdefs
      val _     = processTests (!unitTests, basis)
(* type declarations for consistency checking *)
val _ = op readEvalPrintWith : (string -> unit) ->                     xdef
                                         stream * basis * interactivity -> basis
val _ = op processXDef       : xdef * basis -> basis
  in  basis
  end



(*****************************************************************)
(*                                                               *)
(*   IMPLEMENTATIONS OF \UML\ PRIMITIVES AND DEFINITION OF [[INITIALBASIS]] *)
(*                                                               *)
(*****************************************************************)

(* implementations of \uml\ primitives and definition of [[initialBasis]] S306a *)
(* shared utility functions for building primitives in languages with type inference S266d *)
fun binaryOp f = (fn [a, b] => f (a, b) | _ => raise BugInTypeInference
                                                                      "arity 2")
fun unaryOp  f = (fn [a]    => f  a     | _ => raise BugInTypeInference
                                                                      "arity 1")
fun arithOp f =
      binaryOp (fn (NUM n1, NUM n2) => NUM (f (n1, n2)) 
                 | _ => raise BugInTypeInference "arithmetic on non-numbers")
val arithtype = funtype ([inttype, inttype], inttype)
(* type declarations for consistency checking *)
val _ = op unaryOp  : (value         -> value) -> (value list -> value)
val _ = op binaryOp : (value * value -> value) -> (value list -> value)
val _ = op arithOp   : (int * int -> int) -> (value list -> value)
val _ = op arithtype : ty
(* utility functions for building \nml\ primitives S267a *)
fun comparison f = binaryOp (embedBool o f)
fun intcompare f = 
      comparison (fn (NUM n1, NUM n2) => f (n1, n2)
                   | _ => raise BugInTypeInference "comparing non-numbers")
fun comptype x = funtype ([x, x], booltype)
(* type declarations for consistency checking *)
val _ = op comparison : (value * value -> bool) -> (value list -> value)
val _ = op intcompare : (int   * int   -> bool) -> (value list -> value)
val _ = op comptype   : ty -> ty
val primFunBasis =
  let fun addPrim ((name, prim, tau), (Gamma, Delta, rho)) = 
        ( bindtyscheme (name, generalize (tau, freetyvarsGamma Gamma), Gamma)
        , Delta
        , bind (name, PRIMITIVE prim, rho)
        )
  in  foldl addPrim predefinedTypeBasis (
                                (* primitives for \nml\ and \uml\ [[::]] 490b *)
                                         ("error", unaryOp (fn v => raise
                                                  RuntimeError (valueString v)),
                                                        funtype ([alpha], beta))
                                                                              ::

                               (* primitives for \nml\ and \uml\ [[::]] S319c *)
                                         ("read", unaryOp (fn (SYM s) =>
                                                                let val fd =
                                                                 TextIO.openIn s
                                                                      handle _
                                 => raise RuntimeError ("Cannot read file " ^ s)
                                                                    val sxs =
                                           sxstream (s, filelines fd, noPrompts)
                                                                in  embedList (
                                                               listOfStream sxs)
                                                                    before
                                                               TextIO.closeIn fd
                                                                end
                                                             | _ => raise
                                       BugInTypeInference "read got non-symbol")
                                                , funtype ([symtype], listtype
                                                                     sxtype)) ::

                               (* primitives for \nml\ and \uml\ [[::]] S266e *)
                                         ("+", arithOp op +,   arithtype) :: 
                                         ("-", arithOp op -,   arithtype) :: 
                                         ("*", arithOp op *,   arithtype) :: 
                                         ("/", arithOp op div, arithtype) ::

                               (* primitives for \nml\ and \uml\ [[::]] S267b *)
                                         ("<", intcompare op <,
                                                            comptype inttype) ::
                                         (">", intcompare op >,
                                                            comptype inttype) ::
                                         ("=", comparison primitiveEquality,
                                                              comptype alpha) ::

                               (* primitives for \nml\ and \uml\ [[::]] S267d *)
                                         ("println", unaryOp (fn v => (print (
                                                     valueString v ^ "\n"); v)),
                                                        funtype ([alpha],
                                                                   unittype)) ::
                                         ("print",   unaryOp (fn v => (print (
                                                     valueString v);        v)),
                                                        funtype ([alpha],
                                                                   unittype)) ::
                                         ("printu",  unaryOp (fn NUM n => (
                                                             printUTF8 n; NUM n)
                                                               | _ => raise
                                     BugInTypeInference "printu of non-number"),
                                                        funtype ([inttype],
                                                              unittype)) :: nil)
  end
(* implementations of \uml\ primitives and definition of [[initialBasis]] S306b *)
val initialBasis =
  let val predefinedFuns =
        
         [ ";  predefined uML functions 508 "
         , "(define null? (xs)"
         , "   (case xs"
         , "      [(cons y ys) #t]"
         , "      ['()         #f]))"
         , ";  predefined uML functions 516a "
         , "(data (* * => *) pair"
         , "  [PAIR : (forall ('a 'b) ('a 'b -> (pair 'a 'b)))])"
         , "(val pair PAIR)"
         , "(define fst (p)"
         , "   (case p [(PAIR x _) x]))"
         , "(define snd (p)"
         , "   (case p [(PAIR _ y) y]))"
         , ";  predefined uML functions 525d "
         , "(define compare-ints (n1 n2)"
         , "  (if (< n1 n2) LESS"
         , "      (if (< n2 n1) GREATER"
         , "          EQUAL)))"
         , ";;unboxuml"
         , ";  predefined uML functions 526b "
         , "(define null? (xs)"
         , "   (case xs ['()        #t]"
         , "            [(cons _ _) #f]))"
         , "(define car (xs)"
         , "   (case xs ['()        (error 'car-of-empty-list)]"
         , "            [(cons y _) y]))"
         , "(define cdr (xs)"
         , "   (case xs ['()         (error 'cdr-of-empty-list)]"
         , "            [(cons _ ys) ys]))"
         , ";;unboxuml"
         , ";  predefined uML functions 526c "
         , "(define append (xs ys)"
         , "  (case xs"
         , "     ['()         ys]"
         , "     [(cons z zs) (cons z (append zs ys))]))"
         , ""
         , "(define revapp (xs ys)"
         , "  (case xs"
         , "     ['()         ys]"
         , "     [(cons z zs) (revapp zs (cons z ys))]))"
         , ";  predefined uML functions 526d "
         , "(define list1 (x) (cons x '()))"
         , "(define bind (x y alist)"
         , "  (case alist"
         , "     ['() (list1 (pair x y))]"
         , "     [(cons p ps)"
         , "        (if (= x (fst p))"
         , "            (cons (pair x y) ps)"
         , "            (cons p (bind x y ps)))]))"
         , ";;unboxuml"
         , ";  predefined uML functions 527a "
         , "(define find (x alist)"
         , "  (case alist"
         , "       ['()   NONE]"
         , "       [(cons (PAIR key value) pairs)"
         , "          (if (= x key)"
         , "              (SOME value)"
         , "              (find x pairs))]))"
         , ";;unboxuml"
         , ";  predefined uML functions 527b "
         , "(define bound? (x alist)"
         , "  (case (find x alist)"
         , "     [(SOME _) #t]"
         , "     [NONE     #f]))"
         , ";;unboxuml"
         , ";  predefined uML functions S319f "
         , "(define and (b c) (if b  c  b))"
         , "(define or  (b c) (if b  b  c))"
         , "(define not (b)   (if b #f #t))"
         , ";  predefined uML functions S320a "
         , "(define o (f g) (lambda (x) (f (g x))))"
         , "(define curry   (f) (lambda (x) (lambda (y) (f x y))))"
         , "(define uncurry (f) (lambda (x y) ((f x) y)))"
         , ";  predefined uML functions S320b "
         , "(define caar (xs) (car (car xs)))"
         , "(define cadr (xs) (car (cdr xs)))"
         , "(define cdar (xs) (cdr (car xs)))"
         , ";  predefined uML functions S320c "
         , "(define filter (p? xs)"
         , "  (case xs"
         , "     ('()   '())"
         , "     ((cons y ys)  (if (p? y) (cons y (filter p? ys))"
         , "                              (filter p? ys)))))"
         , ";  predefined uML functions S320d "
         , "(define map (f xs)"
         , "  (case xs"
         , "     ('() '())"
         , "     ((cons y ys) (cons (f y) (map f ys)))))"
         , ";  predefined uML functions S320e "
         , "(define app (f xs)"
         , "  (case xs"
         , "     ('() UNIT)"
         , "     ((cons y ys) (begin (f y) (app f ys)))))"
         , ";  predefined uML functions S320f "
         , "(define reverse (xs) (revapp xs '()))"
         , ";  predefined uML functions S320g "
         , "(define exists? (p? xs)"
         , "  (case xs"
         , "     ('() #f)"
         , "     ((cons y ys) (if (p? y) #t (exists? p? ys)))))"
         , "(define all? (p? xs)"
         , "  (case xs"
         , "     ('() #t)"
         , "     ((cons y ys) (if (p? y) (all? p? ys) #f))))"
         , ";  predefined uML functions S320h "
         , "(define foldr (op zero xs)"
         , "  (case xs"
         , "     ('() zero)"
         , "     ((cons y ys) (op y (foldr op zero ys)))))"
         , "(define foldl (op zero xs)"
         , "  (case xs"
         , "     ('() zero)"
         , "     ((cons y ys) (foldl op (op y zero) ys))))"
         , ";  predefined uML functions S321a "
         , "(define <= (x y) (not (> x y)))"
         , "(define >= (x y) (not (< x y)))"
         , "(define != (x y) (not (= x y)))"
         , ";  predefined uML functions S321b "
         , "(define max (m n) (if (> m n) m n))"
         , "(define min (m n) (if (< m n) m n))"
         , "(define negated (n) (- 0 n))"
         , "(define mod (m n) (- m (* n (/ m n))))"
         , "(define gcd (m n) (if (= n 0) m (gcd n (mod m n))))"
         , "(define lcm (m n) (* m (/ n (gcd m n))))"
         , ";  predefined uML functions S321c "
         , "(define min* (xs) (foldr min (car xs) (cdr xs)))"
         , "(define max* (xs) (foldr max (car xs) (cdr xs)))"
         , "(define gcd* (xs) (foldr gcd (car xs) (cdr xs)))"
         , "(define lcm* (xs) (foldr lcm (car xs) (cdr xs)))"
         , ";  predefined uML functions S321d "
         , "(define list1 (x)               (cons x '()))"
         , "(define list2 (x y)             (cons x (list1 y)))"
         , "(define list3 (x y z)           (cons x (list2 y z)))"
         , "(define list4 (x y z a)         (cons x (list3 y z a)))"
         , "(define list5 (x y z a b)       (cons x (list4 y z a b)))"
         , "(define list6 (x y z a b c)     (cons x (list5 y z a b c)))"
         , "(define list7 (x y z a b c d)   (cons x (list6 y z a b c d)))"
         , "(define list8 (x y z a b c d e) (cons x (list7 y z a b c d e)))"
         , ";  predefined uML functions S321e "
         , "(define takewhile (p? xs)"
         , "  (case xs"
         , "     ('() '())"
         , "     ((cons y ys)"
         , "        (if (p? y)"
         , "            (cons y (takewhile p? ys))"
         , "            '()))))"
         , "(define dropwhile (p? xs)"
         , "  (case xs"
         , "     ('() '())"
         , "     ((cons y ys)"
         , "        (if (p? y)"
         , "            (dropwhile p? ys)"
         , "            xs))))"
          ]
      val xdefs = stringsxdefs ("predefined functions", predefinedFuns)
  in  readEvalPrintWith predefinedFunctionError (xdefs, primFunBasis,
                                                                 noninteractive)
  end


(*****************************************************************)
(*                                                               *)
(*   FUNCTION [[RUNAS]], WHICH EVALUATES STANDARD INPUT GIVEN [[INITIALBASIS]] *)
(*                                                               *)
(*****************************************************************)

(* function [[runAs]], which evaluates standard input given [[initialBasis]] S224d *)
fun runAs interactivity = 
  let val _ = setup_error_format interactivity
      val prompts = if prompts interactivity then stdPrompts else noPrompts
      val xdefs = filexdefs ("standard input", TextIO.stdIn, prompts)
  in  ignore (readEvalPrintWith eprintln (xdefs, initialBasis, interactivity))
  end 
(* type declarations for consistency checking *)
val _ = op runAs : interactivity -> unit


(*****************************************************************)
(*                                                               *)
(*   CODE THAT LOOKS AT COMMAND-LINE ARGUMENTS AND CALLS [[RUNAS]] TO RUN THE INTERPRETER *)
(*                                                               *)
(*****************************************************************)

(* code that looks at command-line arguments and calls [[runAs]] to run the interpreter S225a *)
val _ = case CommandLine.arguments ()
          of []     => runAs (PROMPTING,     PRINTING)
           | ["-q"] => runAs (NOT_PROMPTING, PRINTING)
           | ["-qq"]=> runAs (NOT_PROMPTING, NOT_PRINTING)   (*OMIT*)
           | ["-names"]=> dump_names initialBasis (*OMIT*)
           | _      => eprintln ("Usage: " ^ CommandLine.name () ^ " [-q]")
