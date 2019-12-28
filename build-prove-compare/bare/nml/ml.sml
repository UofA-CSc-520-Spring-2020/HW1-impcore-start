(* ml.sml S270a *)


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
(*   HINDLEY-MILNER TYPES WITH NAMED TYPE CONSTRUCTORS           *)
(*                                                               *)
(*****************************************************************)

(* Hindley-Milner types with named type constructors S266c *)
(* definitions of [[tycon]], [[eqTycon]], and [[tyconString]] for named type constructors 456a *)
type tycon = name
fun eqTycon (mu, mu') = mu = mu'
fun tyconString mu = mu
(* type declarations for consistency checking *)
type tycon = tycon
val _ = op eqTycon : tycon * tycon -> bool
val _ = op tyconString : tycon -> string
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
val funtycon = "function"
(* functions that create or compare Hindley-Milner types with named type constructors 459c *)
val inttype  = TYCON "int"
val booltype = TYCON "bool"
val symtype  = TYCON "sym"
val alpha    = TYVAR "a"
val beta     = TYVAR "b"
val unittype = TYCON "unit"
fun listtype ty = 
  CONAPP (TYCON "list", [ty])
fun pairtype (x, y) =
  CONAPP (TYCON "pair", [x, y])
fun funtype (args, result) = 
  CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args), result])
fun asFuntype (CONAPP (TYCON "function", [CONAPP (TYCON "arguments", args),
                                                                     result])) =
      SOME (args, result)
  | asFuntype _ = NONE
(* type declarations for consistency checking *)
val _ = op inttype   : ty
val _ = op booltype  : ty
val _ = op symtype   : ty
val _ = op alpha     : ty
val _ = op beta      : ty
val _ = op unittype  : ty
val _ = op listtype  : ty -> ty
val _ = op pairtype  : ty * ty -> ty
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



(*****************************************************************)
(*                                                               *)
(*   ABSTRACT SYNTAX AND VALUES FOR \NML                         *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values for \nml S263b *)
(* definitions of [[exp]] and [[value]] for \nml 451a *)
datatype exp = LITERAL of value
             | VAR     of name
             | IFX     of exp * exp * exp
             | BEGIN   of exp list
             | APPLY   of exp * exp list
             | LETX    of let_kind * (name * exp) list * exp
             | LAMBDA  of name list * exp
and let_kind = LET | LETREC | LETSTAR
and (* definition of [[value]] for \nml 451c *)
    value = NIL
          | BOOLV     of bool
          | NUM       of int
          | SYM       of name
          | PAIR      of value * value
          | CLOSURE   of lambda * (unit -> value env)
          | PRIMITIVE of primop
    withtype primop = value list -> value (* raises RuntimeError *)
         and lambda = name list * exp
(* definition of [[def]] for \nml 451b *)
datatype def  = VAL    of name * exp
              | VALREC of name * exp
              | EXP    of exp
              | DEFINE of name * (name list * exp)
(* definition of [[unit_test]] for languages with Hindley-Milner types S263a *)
datatype unit_test = CHECK_EXPECT      of exp * exp
                   | CHECK_ASSERT      of exp
                   | CHECK_ERROR       of exp
                   | CHECK_TYPE        of exp * type_scheme
                   | CHECK_PTYPE       of exp * type_scheme
                   | CHECK_TYPE_ERROR  of def
(* definition of [[xdef]] (shared) S217b *)
datatype xdef = DEF    of def
              | USE    of name
              | TEST   of unit_test
              | DEFS   of def list  (*OMIT*)
(* definition of [[valueString]] for \uscheme, \tuscheme, and \nml 348 *)
fun valueString (SYM v)   = v
  | valueString (NUM n)   = intString n
  | valueString (BOOLV b) = if b then "#t" else "#f"
  | valueString (NIL)     = "()"
  | valueString (PAIR (car, cdr))  = 
      let fun tail (PAIR (car, cdr)) = " " ^ valueString car ^ tail cdr
            | tail NIL = ")"
            | tail v = " . " ^ valueString v ^ ")"
(* type declarations for consistency checking *)
val _ = op valueString : value -> string
      in  "(" ^ valueString car ^ tail cdr
      end
  | valueString (CLOSURE   _) = "<procedure>"
  | valueString (PRIMITIVE _) = "<procedure>"
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
         (*empty*)
  end
fun defName (VAL (x, _))       = x
  | defName (VALREC (x, _)) = x
  | defName (DEFINE (x, _)) = x
  | defName (EXP _) = raise InternalError "asked for name defined by expression"

(* clauses for [[defName]] for forms found only in \uml ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
  (*empty*)


(*****************************************************************)
(*                                                               *)
(*   UTILITY FUNCTIONS ON \USCHEME, \TUSCHEME, AND \NML\ VALUES  *)
(*                                                               *)
(*****************************************************************)

(* utility functions on \uscheme, \tuscheme, and \nml\ values 347b *)
fun embedList []     = NIL
  | embedList (h::t) = PAIR (h, embedList t)
fun embedBool b = BOOLV b
fun bool (BOOLV b) = b
  | bool _         = true
(* type declarations for consistency checking *)
val _ = op embedBool : bool       -> value
val _ = op embedList : value list -> value
val _ = op bool      : value      -> bool
(* utility functions on \uscheme, \tuscheme, and \nml\ values S218a *)
fun equalatoms (NIL,      NIL    )  = true
  | equalatoms (NUM  n1,  NUM  n2)  = (n1 = n2)
  | equalatoms (SYM  v1,  SYM  v2)  = (v1 = v2)
  | equalatoms (BOOLV b1, BOOLV b2) = (b1 = b2)
  | equalatoms  _                   = false
(* type declarations for consistency checking *)
val _ = op equalatoms : value * value -> bool
(* utility functions on \uscheme, \tuscheme, and \nml\ values S218b *)
fun equalpairs (PAIR (car1, cdr1), PAIR (car2, cdr2)) =
      equalpairs (car1, car2) andalso equalpairs (cdr1, cdr2)
  | equalpairs (v1, v2) = equalatoms (v1, v2)
(* type declarations for consistency checking *)
val _ = op equalpairs : value * value -> bool
(* utility functions on \uscheme, \tuscheme, and \nml\ values S218c *)
val testEqual = equalpairs
(* type declarations for consistency checking *)
val _ = op testEqual : value * value -> bool
(* utility functions on \uscheme, \tuscheme, and \nml\ values S232 *)
fun cycleThrough xs =
  let val remaining = ref xs
      fun next () = case !remaining
                      of [] => (remaining := xs; next ())
                       | x :: xs => (remaining := xs; x)
  in  if null xs then
        raise InternalError "empty list given to cycleThrough"
      else
        next
  end
val unspecified =
  cycleThrough [BOOLV true, NUM 39, SYM "this value is unspecified", NIL,
                PRIMITIVE (fn _ => let exception Unspecified in raise
                                                               Unspecified end)]
(* type declarations for consistency checking *)
val _ = op cycleThrough : 'a list -> (unit -> 'a)
val _ = op unspecified  : unit -> value
(* utility functions on \uscheme, \tuscheme, and \nml\ values S267c *)
fun primitiveEquality (v, v') =
 let fun noFun () = raise RuntimeError "compared functions for equality"
 in  case (v, v')
       of (NIL,      NIL    )  => true
        | (NUM  n1,  NUM  n2)  => (n1 = n2)
        | (SYM  v1,  SYM  v2)  => (v1 = v2)
        | (BOOLV b1, BOOLV b2) => (b1 = b2)
        | (PAIR (v, vs), PAIR (v', vs')) =>
            primitiveEquality (v, v') andalso primitiveEquality (vs, vs')
        | (PAIR _,   NIL)    => false
        | (NIL,      PAIR _) => false
        | (CLOSURE   _, _) => noFun ()
        | (PRIMITIVE _, _) => noFun ()
        | (_, CLOSURE   _) => noFun ()
        | (_, PRIMITIVE _) => noFun ()
        | _ => raise BugInTypeInference
                       ("compared incompatible values " ^ valueString v ^
                                                                       " and " ^
                        valueString v' ^ " for equality")
 end
(* utility functions on \uscheme, \tuscheme, and \nml\ values 425a *)
val unitVal = NIL
(* type declarations for consistency checking *)
val _ = op unitVal : value



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
     (* extra case for [[elabdef]] used only in \uml S278f *)
     (* filled in when implementing uML *)
(* type declarations for consistency checking *)
val _ = op elabdef : def * type_env -> type_env * string
(* type declarations for consistency checking *)
val _ = op typeof  : exp * type_env -> ty * con
val _ = op elabdef : def * type_env -> type_env * string



(*****************************************************************)
(*                                                               *)
(*   LEXICAL ANALYSIS AND PARSING FOR \NML, PROVIDING [[FILEXDEFS]] AND [[STRINGSXDEFS]] *)
(*                                                               *)
(*****************************************************************)

(* lexical analysis and parsing for \nml, providing [[filexdefs]] and [[stringsxdefs]] S271b *)
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
(* parsers for \nml\ tokens S271e *)
val arrow = eqx "->" name
val name  = sat (fn n => n <> "->") name  (* an arrow is not a name *)
val tyvar = quote *> (curry op ^ "'" <$> name <?>
                                               "type variable (got quote mark)")
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
(* parsers for Hindley-Milner types with named type constructors S272a *)
val arrows = arrowsOf CONAPP funtype

fun ty tokens = (
     TYCON <$> sat (curry op <> "->") any_name
 <|> TYVAR <$> tyvar
 <|> usageParsers [("(forall (tyvars) type)", bracket ("('a ...)", many tyvar)
                                                                         *> ty)]
     <!> "nested 'forall' type is not a Hindley-Milner type"
 <|> bracket ("constructor application",
              arrows <$> many ty <*>! many (arrow *> many ty))
) tokens

val tyscheme =
      usageParsers [("(forall (tyvars) type)",
                     curry FORALL <$> bracket ("('a ...)", distinctTyvars) <*>
                                                                            ty)]
  <|> curry FORALL [] <$> ty
  <?> "type"
(* type declarations for consistency checking *)
val _ = op tyvar : string parser
val _ = op ty    : ty     parser
(* parsers and [[xdef]] streams for \nml S271c *)
fun exptable exp =
  let val bindings = bindingsOf "(x e)" name exp
      val dbs      = distinctBsIn bindings
      fun letx kind bs exp = LETX (kind, bs, exp)
      val formals = formalsOf "(x1 x2 ...)" name "lambda"
(* type declarations for consistency checking *)
val _ = op exp      : exp parser
val _ = op exptable : exp parser -> exp parser
  in usageParsers
     [ ("(if e1 e2 e3)",            curry3 IFX          <$> exp <*> exp <*> exp)
     , ("(begin e1 ...)",                  BEGIN        <$> many exp)
     , ("(lambda (names) body)",    curry  LAMBDA       <$> formals      <*> exp
                                                                               )
     , ("(let (bindings) body)",    curry3 LETX LET     <$> dbs "let"    <*> exp
                                                                               )
     , ("(letrec (bindings) body)", curry3 LETX LETREC  <$> dbs "letrec" <*> exp
                                                                               )
     , ("(let* (bindings) body)",   curry3 LETX LETSTAR <$> bindings     <*> exp
                                                                               )
     (* rows added to \nml's [[exptable]] in exercises S271d *)
     (* add syntactic extensions here, each preceded by a comma *)
     ]
  end

val exp = fullSchemeExpOf (atomicSchemeExpOf name) exptable
(* parsers and [[xdef]] streams for \nml S272b *)
val deftable = usageParsers
  [ ("(define f (args) body)",
                  let val formals = formalsOf "(x1 x2 ...)" name "define"
                  in  curry DEFINE <$> name <*> (pair <$> formals <*> exp)
                  end)
  , ("(val x e)",     curry VAL    <$> name <*> exp)
  , ("(val-rec x e)", curry VALREC <$> name <*> exp)
  ]

val testtable = usageParsers
  [ ("(check-expect e1 e2)",         curry CHECK_EXPECT <$> exp <*> exp)
  , ("(check-assert e)",                   CHECK_ASSERT <$> exp)
  , ("(check-error e)",                    CHECK_ERROR  <$> exp)
  , ("(check-type e tau)",           curry CHECK_TYPE   <$> exp <*> tyscheme)
  , ("(check-principal-type e tau)", curry CHECK_PTYPE  <$> exp <*> tyscheme)
  , ("(check-type-error e)",               CHECK_TYPE_ERROR <$> (deftable <|>
                                                                 EXP <$> exp))
  ]

val xdeftable = usageParsers
  [ ("(use filename)", USE <$> name)
  (* rows added to \nml's [[xdeftable]] in exercises S272c *)
  (* add syntactic extensions here, each preceded by a comma *)
  ]

val xdef  =  TEST <$> testtable
         <|> DEF  <$> deftable
         <|>          xdeftable
         <|> badRight "unexpected right bracket"
         <|> DEF <$> EXP <$> exp
         <?> "definition"
(* parsers and [[xdef]] streams for \nml S272d *)
val xdefstream = interactiveParsedStream (schemeToken, xdef)
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
(*   EVALUATION, TESTING, AND THE READ-EVAL-PRINT LOOP FOR \NML  *)
(*                                                               *)
(*****************************************************************)

(* evaluation, testing, and the read-eval-print loop for \nml S264a *)
(* definition of [[namedValueString]] for functional bridge languages S258a *)
fun namedValueString x v =
  case v of CLOSURE _ => x
          | PRIMITIVE _ => x
          | _ => valueString v
(* type declarations for consistency checking *)
val _ = op namedValueString : name -> value -> string
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
  (* clause for [[evaldef]] for datatype definition (\uml\ only) S266b *)
  (* code goes here in Chapter 11 *)
(* type declarations for consistency checking *)
val _ = op evaldef : def * value env -> value env * string
(* definitions of [[basis]] and [[processDef]] for \nml S268c *)
type basis = type_env * value env
fun processDef (d, (Gamma, rho), interactivity) =
  let val (Gamma, tystring)  = elabdef (d, Gamma)
      val (rho,   valstring) = evaldef (d, rho)
      val _ = if prints interactivity then
                println (valstring ^ " : " ^ tystring)
              else
                ()
(* type declarations for consistency checking *)
val _ = op processDef : def * basis * interactivity -> basis
  in  (Gamma, rho)
  end
fun dump_names (types, values) = app (println o fst) values  (*OMIT*)
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
(* definition of [[testIsGood]] for \nml S273a *)
(* definition of [[skolemTypes]] for languages with named type constructors S274c *)
val skolemTypes = streamMap (fn n => TYCON ("skolem type " ^ intString n))
                                                                        naturals
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
fun testIsGood (test, (Gamma, rho)) =
  let fun ty e = typeof (e, Gamma)
                 handle NotFound x =>
                   raise TypeError ("name " ^ x ^ " is not defined")
      fun deftystring d =
        snd (elabdef (d, Gamma))
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
      fun checks (CHECK_EXPECT (e1, e2)) = checkExpectChecks (e1, e2)
        | checks (CHECK_ASSERT e)        = checkAssertChecks e
        | checks (CHECK_ERROR e)         = checkErrorChecks e
        | checks (CHECK_TYPE  (e, tau))  = checkTypeChecks "check-type" (e, tau)
        | checks (CHECK_PTYPE (e, tau))  = checkTypeChecks
                                                          "check-principal-type"
                                                                        (e, tau)
        | checks (CHECK_TYPE_ERROR e)    = true

      fun outcome e = withHandlers (fn () => OK (eval (e, rho))) () (ERROR o
                                                                     stripAtLoc)

   (* [[asSyntacticValue]] for \uscheme, \timpcore, \tuscheme, and \nml S231b *)
      fun asSyntacticValue (LITERAL v) = SOME v
        | asSyntacticValue _           = NONE
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
      fun passes (CHECK_EXPECT (c, e))  = checkExpectPasses (c, e)
        | passes (CHECK_ASSERT c)       = checkAssertPasses c
        | passes (CHECK_ERROR c)        = checkErrorPasses  c
        | passes (CHECK_TYPE  (c, tau)) = checkTypePasses          (c, tau)
        | passes (CHECK_PTYPE (c, tau)) = checkPrincipalTypePasses (c, tau)
        | passes (CHECK_TYPE_ERROR c)   = checkTypeErrorPasses c

  in  checks test andalso passes test
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
(*   IMPLEMENTATIONS OF \NML\ PRIMITIVES AND DEFINITION OF [[INITIALBASIS]] *)
(*                                                               *)
(*****************************************************************)

(* implementations of \nml\ primitives and definition of [[initialBasis]] S269c *)
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
val initialBasis =
  let fun addPrim ((name, prim, tau), (Gamma, rho)) = 
        ( bindtyscheme (name, generalize (tau, freetyvarsGamma Gamma), Gamma)
        , bind (name, PRIMITIVE prim, rho)
        )
      val primBasis = foldl addPrim (emptyTypeEnv, emptyEnv) 
                         ((* primitives for \nml\ and \uml\ [[::]] 490b *)
                          ("error", unaryOp (fn v => raise RuntimeError (
                                                                valueString v)),
                                         funtype ([alpha], beta)) ::
                          (* primitives for \nml\ and \uml\ [[::]] S266e *)
                          ("+", arithOp op +,   arithtype) :: 
                          ("-", arithOp op -,   arithtype) :: 
                          ("*", arithOp op *,   arithtype) :: 
                          ("/", arithOp op div, arithtype) ::
                          (* primitives for \nml\ and \uml\ [[::]] S267b *)
                          ("<", intcompare op <,              comptype inttype)
                                                                              ::
                          (">", intcompare op >,              comptype inttype)
                                                                              ::
                          ("=", comparison primitiveEquality, comptype alpha) ::
                          (* primitives for \nml\ and \uml\ [[::]] S267d *)
                          ("println", unaryOp (fn v => (print (valueString v ^
                                                                     "\n"); v)),
                                         funtype ([alpha], unittype)) ::
                          ("print",   unaryOp (fn v => (print (valueString v);
                                                                            v)),
                                         funtype ([alpha], unittype)) ::
                          ("printu",  unaryOp (fn NUM n => (printUTF8 n; NUM n)
                                                | _ => raise BugInTypeInference
                                                        "printu of non-number"),
                                         funtype ([inttype], unittype)) :: 
                          (* primitives for \nml\ [[::]] 490a *)
                          ("null?", unaryOp  (fn NIL => BOOLV true | _ => BOOLV
                                                                         false),
                                                  funtype ([listtype alpha],
                                                                   booltype)) ::
                          ("cons",  binaryOp (fn (a, b) => PAIR (a, b)),
                                                  funtype ([alpha, listtype
                                                     alpha], listtype alpha)) ::
                          ("car",   unaryOp  (fn (PAIR (car, _)) => car 
                                               | NIL => raise RuntimeError
                                                     "car applied to empty list"
                                               | _   => raise BugInTypeInference
                                                     "car applied to non-list"),
                                                  funtype ([listtype alpha],
                                                                      alpha)) ::
                          ("cdr",   unaryOp  (fn (PAIR (_, cdr)) => cdr 
                                               | NIL => raise RuntimeError
                                                     "cdr applied to empty list"
                                               | _   => raise BugInTypeInference
                                                     "cdr applied to non-list"),
                                                  funtype ([listtype alpha],
                                                             listtype alpha)) ::
                          [])
      val fundefs = 
                     [ ";  predefined {\\nml} functions S268a "
                     , "(define list1 (x) (cons x '()))"
                     , "(define bind (x y alist)"
                     , "  (if (null? alist)"
                     , "    (list1 (pair x y))"
                     , "    (if (= x (fst (car alist)))"
                     , "      (cons (pair x y) (cdr alist))"
                     , "      (cons (car alist) (bind x y (cdr alist))))))"
                     , ";  predefined {\\nml} functions S268b "
                     , "(define bound? (x alist)"
                     , "  (if (null? alist) "
                     , "    #f"
                     , "    (if (= x (fst (car alist)))"
                     , "      #t"
                     , "      (bound? x (cdr alist)))))"
                     , "(define find (x alist)"
                     , "  (if (null? alist) "
                     , "    (error 'not-found)"
                     , "    (if (= x (fst (car alist)))"
                     , "      (snd (car alist))"
                     , "      (find x (cdr alist)))))"
                     , ";  predefined {\\nml} functions S277a "
                     , "(define caar (xs) (car (car xs)))"
                     , "(define cadr (xs) (car (cdr xs)))"
                     , "(define cdar (xs) (cdr (car xs)))"
                     , "(define and (b c) (if b  c  b))"
                     , "(define or  (b c) (if b  b  c))"
                     , "(define not (b)   (if b #f #t))"
                     , ";  predefined {\\nml} functions S277b "
                     , "(define append (xs ys)"
                     , "  (if (null? xs)"
                     , "     ys"
                     , "     (cons (car xs) (append (cdr xs) ys))))"
                     , "(define revapp (xs ys)"
                     , "  (if (null? xs)"
                     , "     ys"
                     , "     (revapp (cdr xs) (cons (car xs) ys))))"
                     , "(define reverse (xs) (revapp xs '()))"
                     , ";  predefined {\\nml} functions S277c "
                     , "(define o (f g) (lambda (x) (f (g x))))"
                     , "(define curry   (f) (lambda (x) (lambda (y) (f x y))))"
                     , "(define uncurry (f) (lambda (x y) ((f x) y)))"
                     , ";  predefined {\\nml} functions S277d "
                     , "(define filter (p? xs)"
                     , "  (if (null? xs)"
                     , "    '()"
                     , "    (if (p? (car xs))"
                     , "      (cons (car xs) (filter p? (cdr xs)))"
                     , "      (filter p? (cdr xs)))))"
                     , ";  predefined {\\nml} functions S277e "
                     , "(define map (f xs)"
                     , "  (if (null? xs)"
                     , "    '()"
                     , "    (cons (f (car xs)) (map f (cdr xs)))))"
                     , ";  predefined {\\nml} functions S277f "
                     , "(define exists? (p? xs)"
                     , "  (if (null? xs)"
                     , "    #f"
                     , "    (if (p? (car xs)) "
                     , "      #t"
                     , "      (exists? p? (cdr xs)))))"
                     , "(define all? (p? xs)"
                     , "  (if (null? xs)"
                     , "    #t"
                     , "    (if (p? (car xs))"
                     , "      (all? p? (cdr xs))"
                     , "      #f)))"
                     , ";  predefined {\\nml} functions S278a "
                     , "(define foldr (op zero xs)"
                     , "  (if (null? xs)"
                     , "    zero"
                     , "    (op (car xs) (foldr op zero (cdr xs)))))"
                     , "(define foldl (op zero xs)"
                     , "  (if (null? xs)"
                     , "    zero"
                     , "    (foldl op (op (car xs) zero) (cdr xs))))"
                     , ";  predefined {\\nml} functions S278b "
                     , "(define <= (x y) (not (> x y)))"
                     , "(define >= (x y) (not (< x y)))"
                     , "(define != (x y) (not (= x y)))"
                     , ";  predefined {\\nml} functions S278c "
                     , "(define max (x y) (if (> x y) x y))"
                     , "(define min (x y) (if (< x y) x y))"
                     , "(define negated (n) (- 0 n))"
                     , "(define mod (m n) (- m (* n (/ m n))))"
                     , "(define gcd (m n) (if (= n 0) m (gcd n (mod m n))))"
                     , "(define lcm (m n) (* m (/ n (gcd m n))))"
                     , ";  predefined {\\nml} functions S278d "
                     , "(define min* (xs) (foldr min (car xs) (cdr xs)))"
                     , "(define max* (xs) (foldr max (car xs) (cdr xs)))"
                     , "(define gcd* (xs) (foldr gcd (car xs) (cdr xs)))"
                     , "(define lcm* (xs) (foldr lcm (car xs) (cdr xs)))"
                     , ";  predefined {\\nml} functions S278e "
                     , "(define list1 (x)               (cons x '()))"
                     , "(define list2 (x y)             (cons x (list1 y)))"
                     , "(define list3 (x y z)           (cons x (list2 y z)))"
                     , "(define list4 (x y z a)         (cons x (list3 y z a)))"
                     ,
                     "(define list5 (x y z a b)       (cons x (list4 y z a b)))"
                     ,
                   "(define list6 (x y z a b c)     (cons x (list5 y z a b c)))"
                     ,
                 "(define list7 (x y z a b c d)   (cons x (list6 y z a b c d)))"
                     ,
               "(define list8 (x y z a b c d e) (cons x (list7 y z a b c d e)))"
                      ]
      val xdefs   = stringsxdefs ("predefined functions", fundefs)
  in  readEvalPrintWith predefinedFunctionError (xdefs, primBasis,
                                                                 noninteractive)
  end
(* type declarations for consistency checking *)
val _ = op initialBasis : type_env * value env


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
