(* usm.sml S473 *)


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
(*   ABSTRACT SYNTAX AND VALUES FOR \USMALLTALK                  *)
(*                                                               *)
(*****************************************************************)

(* abstract syntax and values for \usmalltalk S472a *)
(* support for \usmalltalk\ stack frames S478a *)
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
(* definitions of [[exp]], [[rep]], and [[class]] for \usmalltalk 773b *)
datatype rep = USER     of value ref env (* ordinary object *)
             | ARRAY    of value Array.array
             | NUM      of int
             | SYM      of name
             | CLOSURE  of name list * exp list * value ref env * class * frame
             | CLASSREP of class
             | METHOD   of method
(* definitions of [[exp]], [[rep]], and [[class]] for \usmalltalk 774b *)
and class  = CLASS of { name    : name            (* name of the class *)
                      , super   : class option    (* superclass, if any *)
                      , ivars   : string list     (* instance variables *)
                      , methods : method env ref
                                                 (* both exported and private *)
                      , class   : metaclass ref
                                                 (* class of the class object *)
                      }
and metaclass = META of class | PENDING
(* definitions of [[exp]], [[rep]], and [[class]] for \usmalltalk 776a *)
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
(* definitions of [[value]] and [[method]] for \usmalltalk 773a *)
withtype value = class * rep
(* definitions of [[value]] and [[method]] for \usmalltalk 774c *)
and method = { name : name, formals : name list, locals : name list, body : exp
             , superclass : class (* used to send messages to super *)
             }

(* definition of [[def]] for \usmalltalk 775b *)
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
(* definition of [[unit_test]] for \usmalltalk S472b *)
(* definition of [[unit_test]] for untyped languages (shared) S217a *)
datatype unit_test = CHECK_EXPECT of exp * exp
                   | CHECK_ASSERT of exp
                   | CHECK_ERROR  of exp
             | CHECK_PRINT of exp * string
(* definition of [[xdef]] (shared) S217b *)
datatype xdef = DEF    of def
              | USE    of name
              | TEST   of unit_test
              | DEFS   of def list  (*OMIT*)
fun className (CLASS {name, ...}) = name
(* definition of [[valueString]] for \usmalltalk S498c *)
fun valueString (c, NUM n) = intString n ^ valueString(c, USER [])
  | valueString (_, SYM v) = v
  | valueString (c, _) = "<" ^ className c ^ ">"
(* definition of [[expString]] for \usmalltalk S501 *)
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

(* support for logging (for coverage analysis) S474 *)
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

(* utility functions on \usmalltalk\ classes, methods, and values 774a *)
fun instanceVars (_, USER rep) = rep
  | instanceVars self = bind ("self", ref self, emptyEnv)
(* type declarations for consistency checking *)
val _ = op instanceVars : value -> value ref env
(* utility functions on \usmalltalk\ classes, methods, and values S476a *)
fun valueSelector [] = "value"
  | valueSelector args = concat (map (fn _ => "value:") args)
(* utility functions on \usmalltalk\ classes, methods, and values S476b *)
fun className (CLASS {name,  ...}) = name
fun classId   (CLASS {class, ...}) = class
(* type declarations for consistency checking *)
val _ = op className : class -> name
val _ = op classId   : class -> metaclass ref
(* utility functions on \usmalltalk\ classes, methods, and values S476c *)
fun methodName ({ name, ... } : method) = name
fun methodsEnv ms = foldl (fn (m, rho) => bind (methodName m, m, rho)) emptyEnv
                                                                              ms
(* type declarations for consistency checking *)
val _ = op methodName   : method -> name
val _ = op methodsEnv   : method list -> method env
(* utility functions on \usmalltalk\ classes, methods, and values S476d *)
fun mkClass name meta super ivars ms =
  (
(* if any name in [[ivars]] repeats a name declared in a superclass, raise [[RuntimeError]] S476e *)
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
(* type declarations for consistency checking *)
val _ = op mkClass : name -> metaclass -> class -> name list -> method list ->
                                                                           class



(*****************************************************************)
(*                                                               *)
(*   SUPPORT FOR BOOTSTRAPPING CLASSES AND VALUES USED DURING PARSING *)
(*                                                               *)
(*****************************************************************)

(* support for bootstrapping classes and values used during parsing 787a *)
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
(* type declarations for consistency checking *)
val _ = op mkInteger : int        -> value
val _ = op mkSymbol  : string     -> value
val _ = op mkArray   : value list -> value
(* support for bootstrapping classes and values used during parsing 787b *)
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
(* type declarations for consistency checking *)
val _ = op findClass : string * value ref env -> class
(* support for bootstrapping classes and values used during parsing 788a *)
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
(* type declarations for consistency checking *)
val _ = op mkBoolean : bool -> value
(* support for bootstrapping classes and values used during parsing S478c *)
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
(* type declarations for consistency checking *)
val _ = op mkBlock : name list * exp list * value ref env * class * frame ->
                                                                           value
(* support for bootstrapping classes and values used during parsing S484b *)
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

(* lexical analysis and parsing for \usmalltalk, providing [[filexdefs]] and [[stringsxdefs]] S489a *)
(* lexical analysis for \usmalltalk S489b *)
val nullsrc : srcloc = ("internally generated SEND node", 1)
(* lexical analysis for \usmalltalk S489c *)
datatype pretoken = INTCHARS of char list
                  | NAME     of name
                  | QUOTE    of string option (* symbol or array *)
type token = pretoken plus_brackets
(* lexical analysis for \usmalltalk S489d *)
fun pretokenString (INTCHARS ds)    = implode ds
  | pretokenString (NAME    x)      = x
  | pretokenString (QUOTE NONE)     = "'"
  | pretokenString (QUOTE (SOME s)) = "'" ^ s
(* lexical analysis for \usmalltalk S489e *)
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
(* type declarations for consistency checking *)
val _ = op smalltalkToken : token lexer
end
(* parsers for single \usmalltalk\ tokens S490b *)
type 'a parser = (token, 'a) polyparser
val token : token parser = token (* make it monomorphic *)
val pretoken  = (fn (PRETOKEN t)=> SOME t  | _ => NONE) <$>? token
val name = (fn (NAME s)         => SOME s  | _ => NONE) <$>? pretoken
val intchars = (fn (INTCHARS ds)=> SOME ds | _ => NONE) <$>? pretoken
val sym  = (fn (QUOTE (SOME s)) => SOME s  | _ => NONE) <$>? pretoken
val quote= (fn (QUOTE NONE    ) => SOME () | _ => NONE) <$>? pretoken
val any_name = name

val int = intFromChars <$>! intchars

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
(* parsers and [[xdef]] streams for \usmalltalk S490a *)
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
(* parsers and [[xdef]] streams for \usmalltalk S490c *)
fun isImmutable x =
  List.exists (fn x' => x' = x) ["true", "false", "nil", "self", "super"] 
val immutable = sat isImmutable name

val mutable =
  let fun can'tMutate (loc, x) =
        ERROR (srclocString loc ^
               ": you cannot set or val-bind pseudovariable " ^ x)
  in  can'tMutate <$>! @@ immutable <|> OK <$>! name
  end
(* parsers and [[xdef]] streams for \usmalltalk S491a *)
val atomicExp =  LITERAL <$> NUM    <$> int
             <|> LITERAL <$> SYM    <$> (sym <|> (quote *> name)
                                             <|> (quote *> (intString <$> int)))
             <|> SUPER              <$  eqx "super" name
             <|> VAR                <$> name
(* parsers and [[xdef]] streams for \usmalltalk S491b *)
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
(* parsers and [[xdef]] streams for \usmalltalk S491c *)
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
(* parsers and [[xdef]] streams for \usmalltalk S492a *)
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
(* type declarations for consistency checking *)
val _ = op name : string parser
val _ = op int  : int    parser
(* type declarations for consistency checking *)
val _ = op exp      : exp parser
val _ = op quotelit : value parser
(* type declarations for consistency checking *)
val _ = op quotelit : value parser
(* parsers and [[xdef]] streams for \usmalltalk S492b *)
val printable = name <|> implode <$> intchars

val testtable = usageParsers
  [ ("(check-expect e1 e2)", curry CHECK_EXPECT <$> exp <*> exp)
  , ("(check-assert e)",           CHECK_ASSERT <$> exp)
  , ("(check-error e)",            CHECK_ERROR  <$> exp)
  , ("(check-print e chars)", curry CHECK_PRINT <$> exp <*> printable)
  ]
(* type declarations for consistency checking *)
val _ = op testtable : unit_test parser
(* parsers and [[xdef]] streams for \usmalltalk S492c *)
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
(* type declarations for consistency checking *)
val _ = op method : method_def parser
val parseMethods = many method <* many eol <* eos
(* parsers and [[xdef]] streams for \usmalltalk S493a *)
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
(* type declarations for consistency checking *)
val _ = op deftable : def parser
(* parsers and [[xdef]] streams for \usmalltalk S493b *)
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
(* type declarations for consistency checking *)
val _ = op xdeftable : xdef parser
val _ = op xdef      : xdef parser
(* parsers and [[xdef]] streams for \usmalltalk S493c *)
val xdefstream = interactiveParsedStream (smalltalkToken, xdef)
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
(*   EVALUATION, TESTING, AND THE READ-EVAL-PRINT LOOP FOR \USMALLTALK *)
(*                                                               *)
(*****************************************************************)

(* evaluation, testing, and the read-eval-print loop for \usmalltalk S487b *)
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
(* support for primitives and built-in classes S475a *)
(* utility functions for building primitives in \usmalltalk S479a *)
type primitive = value list * value ref env -> value
fun arityError n args =
  raise RuntimeError ("primitive expected " ^ intString n ^
                      " arguments; got " ^ intString (length args))
fun unaryPrim  f = (fn ([a],    _) => f  a     | (vs, _) => arityError 0 vs) :
                                                                       primitive
fun binaryPrim f = (fn ([a, b], _) => f (a, b) | (vs, _) => arityError 1 vs) :
                                                                       primitive
(* type declarations for consistency checking *)
val _ = op unaryPrim  : (value         -> value) -> primitive
val _ = op binaryPrim : (value * value -> value) -> primitive
(* utility functions for building primitives in \usmalltalk S479b *)
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
(* type declarations for consistency checking *)
val _ = op internalParse : 'a parser -> string list -> 'a
(* metaclass utilities 784b *)
fun metaclass (CLASS { class = ref meta, ... }) =
  case meta of META c => c
             | PENDING => raise InternalError "pending class"

fun classObject c = (metaclass c, CLASSREP c)
(* type declarations for consistency checking *)
val _ = op metaclass   : class -> class
val _ = op classObject : class -> value
(* metaclass utilities S476f *)
fun setMeta (CLASS { class = m as ref PENDING, ... }, meta) = m := META meta
  | setMeta (CLASS { class = ref (META _), ... }, _) =
      raise InternalError "double patch"
(* \ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives S460c *)
fun errorPrim msg = fn _ => raise RuntimeError msg
(* \ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives S477a *)
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
(* type declarations for consistency checking *)
val _ = op methodDefns : class * class -> method_def list -> method list *
                                                                     method list
val _ = op method : method_def -> method
  in  foldr addMethodDefn ([], []) ms
  end
(* \ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives S477b *)
fun findClass (supername, xi) =
  case !(find (supername, xi))
    of (meta, CLASSREP c) => (meta, c)
     | v => raise RuntimeError ("object " ^ supername ^ " = " ^ valueString v ^
                                " is not a class")
(* type declarations for consistency checking *)
val _ = op findClass : name * value ref env -> class * class
(* \ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives S481a *)
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
(* type declarations for consistency checking *)
val _ = op eqRep : value * value -> bool
(* \ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives S481b *)
fun memberOf ((c, _), (_, CLASSREP c')) = mkBoolean (classId c = classId c')
  | memberOf _ = raise RuntimeError "argument of isMemberOf: must be a class"

fun kindOf ((c, _), (_, CLASSREP (CLASS {class=u', ...}))) =
      let fun subclassOfClassU' (CLASS {super, class=u, ... }) =
            u = u' orelse (case super of NONE => false | SOME c =>
                                                            subclassOfClassU' c)
      in  mkBoolean (subclassOfClassU' c)
      end
  | kindOf _ = raise RuntimeError "argument of isKindOf: must be a class"
(* \ml\ functions for [[Object]]'s and [[UndefinedObject]]'s primitives S481c *)
fun error (_, (_, SYM s)) = raise RuntimeError s
  | error (_, (c, _    )) =
      raise RuntimeError ("error: got class " ^ className c ^
                                                            "; expected Symbol")
(* utility functions for parsing internal method definitions S475b *)
val bogusSuperclass = CLASS { name = "bogus superclass", super = NONE
                            , ivars = [], methods = ref [ ], class = ref PENDING
                            }
val internalMethodDefns = methodDefns (bogusSuperclass, bogusSuperclass)
fun internalMethods strings =
  case (internalMethodDefns o internalParse parseMethods) strings
    of ([], imethods) => imethods 
     | (_ :: _, _) => raise InternalError "primitive class has class methods"
(* built-in class [[Object]] 785a *)
val objectMethods = internalMethods 
                                     [ ";  methods of class [[Object]] 720 "
                                     ,
                  "(method ==  (anObject) (primitive sameObject self anObject))"
                                     ,
                              "(method !== (anObject) ((self == anObject) not))"
                                     , ";  methods of class [[Object]] 721a "
                                     ,
                                     "(method =  (anObject) (self == anObject))"
                                     ,
                                "(method != (anObject) ((self = anObject) not))"
                                     , ";  methods of class [[Object]] 742b "
                                     , "(method isNil  () false)"
                                     , "(method notNil () true)"
                                     , ";  methods of class [[Object]] S460a "
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
(* built-in class [[UndefinedObject]] and value [[nilValue]] 785b *)
val nilClass = 
  mkClass "UndefinedObject" PENDING objectClass []
    (internalMethods 
                      [ ";  methods of class [[UndefinedObject]] 742a "
                      , "(method isNil  () true)"
                      , "(method notNil () false)"
                      , ";  methods of class [[UndefinedObject]] S461c "
                      , "(method print () ('nil print) self)"
                       ])
(* built-in class [[UndefinedObject]] and value [[nilValue]] 785c *)
val nilValue = 
  let val nilCell  = ref (nilClass, USER []) : value ref
      val nilValue = (nilClass, USER (bind ("self", nilCell, emptyEnv)))
      val _        = nilCell := nilValue
  in  nilValue
  end
(* \ml\ functions for remaining classes' primitives 779b *)
type closure = name list * exp list * value ref env * class * frame
val applyClosureRef : (closure * value list * value ref env -> value) ref
  = ref (fn _ => raise InternalError "applyClosureRef not set")

fun valuePrim ((_, CLOSURE clo) :: vs, xi) = !applyClosureRef (clo, vs, xi)
  | valuePrim _ = raise RuntimeError "primitive `value` needs a closure"
(* \ml\ functions for remaining classes' primitives 788b *)
val classPrimitive = unaryPrim (fn (c, rep) => classObject c)
(* \ml\ functions for remaining classes' primitives 789 *)
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
(* type declarations for consistency checking *)
val _ = op mkIvars       : class -> value ref env
val _ = op newUserObject : class -> value
end
(* \ml\ functions for remaining classes' primitives S479c *)
fun classPrim f = 
  unaryPrim (fn (meta, CLASSREP c) => f (meta, c)
              | _ => raise RuntimeError "class primitive sent to non-class")
(* type declarations for consistency checking *)
val _ = op classPrim : (class * class -> value) -> primitive
(* \ml\ functions for remaining classes' primitives S479d *)
fun superclassObject (_, CLASS { super = NONE, ... })   = nilValue
  | superclassObject (_, CLASS { super = SOME c, ... }) = classObject c
(* \ml\ functions for remaining classes' primitives S480a *)
fun withOverflow binop ([(_, NUM n), (_, NUM m), ovflw], xi) =
      (mkBlock ([], [VALUE (mkInteger (binop (n, m)))], emptyEnv, objectClass,
                                                                        noFrame)
       handle Overflow => ovflw)
  | withOverflow _ ([_, _, _], _) =
      raise RuntimeError "numeric primitive with overflow expects numbers"
  | withOverflow _ _ =
      raise RuntimeError "numeric primitive with overflow expects 3 arguments"
(* \ml\ functions for remaining classes' primitives S481d *)
fun printInt (self as (_, NUM n)) = ( xprint (intString n); self )
  | printInt _ = raise RuntimeError (
                                   "cannot print when object inherits from Int")
(* \ml\ functions for remaining classes' primitives S481e *)
fun printu (self as (_, NUM n)) = ( printUTF8 n; self )
  | printu _ = raise RuntimeError ("receiver of printu is not a small integer")
(* \ml\ functions for remaining classes' primitives S482a *)
fun binaryInt mk operator ((_, NUM n), (_, NUM m)) = mk (operator (n, m))
  | binaryInt _ _         ((_, NUM n), (c, _)) =
      raise RuntimeError ("numeric primitive expected numeric argument, got <"
                          ^ className c ^ ">")
  | binaryInt _ _         ((c, _), _) =
      raise RuntimeError ("numeric primitive method defined on <" ^ className c
                                                                          ^ ">")
fun arithop    operator = binaryPrim (binaryInt mkInteger operator)
fun intcompare operator = binaryPrim (binaryInt mkBoolean operator)
(* type declarations for consistency checking *)
val _ = op binaryInt  : ('a -> value) -> (int * int -> 'a)   -> value * value ->
                                                                           value
val _ = op arithop    :                  (int * int -> int)  -> primitive
val _ = op intcompare :                  (int * int -> bool) -> primitive
(* \ml\ functions for remaining classes' primitives S482b *)
fun newInteger ((_, CLASSREP c), (_, NUM n)) = (c, NUM n)
  | newInteger _ = raise RuntimeError (
                                   "made new integer with non-int or non-class")
(* \ml\ functions for remaining classes' primitives S482d *)
fun printSymbol (self as (_, SYM s)) = (xprint s; self)
  | printSymbol _ = raise RuntimeError
                                 "cannot print when object inherits from Symbol"
(* \ml\ functions for remaining classes' primitives S482e *)
fun newSymbol ((_, CLASSREP c), (_, SYM s)) = (c, SYM s)
  | newSymbol _ = raise RuntimeError (
                                 "made new symbol with non-symbol or non-class")
(* \ml\ functions for remaining classes' primitives S483b *)
fun newArray ((_, CLASSREP c), (_, NUM n)) = (c, ARRAY (Array.array (n, nilValue
                                                                             )))
  | newArray _ = raise RuntimeError
                                "Array new sent to non-class or got non-integer"
(* \ml\ functions for remaining classes' primitives S483c *)
fun arrayPrimitive f ((c, ARRAY a) :: vs, _) = f (a, vs)
  | arrayPrimitive f _ = raise RuntimeError "Array primitive used on non-array"

fun arraySize (a, []) = mkInteger (Array.length a)
  | arraySize (a, vs) = arityError 0 vs
(* type declarations for consistency checking *)
val _ = op arrayPrimitive : (value array * value list -> value) -> primitive
(* \ml\ functions for remaining classes' primitives S483d *)
fun arrayAt (a, [(_, NUM n)]) = Array.sub (a, n)
  | arrayAt (_, [_])  = raise RuntimeError "Non-integer used as array subscript"
  | arrayAt (_, vs)   = arityError 1 vs

fun arrayUpdate (a, [(_, NUM n), x]) = (Array.update (a, n, x); nilValue)
  | arrayUpdate (_, [_, _]) = raise RuntimeError
                                           "Non-integer used as array subscript"
  | arrayUpdate (_, vs)     = arityError 2 vs
(* \ml\ functions for remaining classes' primitives S484a *)
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
(* \ml\ functions for remaining classes' primitives S484c *)
fun methodNames (_, CLASS { methods, ... }) = mkArray (map (mkSymbol o fst) (!
                                                                       methods))
(* \ml\ functions for remaining classes' primitives S485a *)
fun getMethod ((_, CLASSREP (c as CLASS { methods, name, ... })), (_, SYM s)) =
      (mkCompiledMethod (find (s, !methods))
       handle NotFound _ =>
         raise RuntimeError ("class " ^ className c ^ " has no method " ^ s))
      before (if logging then logGetMethod name s else ())
  | getMethod ((_, CLASSREP _), _) =
      raise RuntimeError "getMethod primitive given non-name"    
  | getMethod _ =
      raise RuntimeError "getMethod primitive given non-class"    
(* \ml\ functions for remaining classes' primitives S485b *)
fun removeMethod ((_, CLASSREP (c as CLASS { methods, ... })), (_, SYM s)) =
      (methods := List.filter (fn (m, _) => m <> s) (!methods); nilValue)
  | removeMethod ((_, CLASSREP _), _) =
      raise RuntimeError "removeMethod primitive given non-name"    
  | removeMethod _ =
      raise RuntimeError "removeMethod primitive given non-class"    
(* \ml\ functions for remaining classes' primitives S485c *)
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
(* built-in classes [[Class]] and [[Metaclass]] 785d *)
val classClass =
  mkClass "Class" PENDING objectClass []
    (internalMethods 
                      [ ";  methods of class [[Class]] 785e "
                      , "(method new () (primitive newUserObject self))"
                      , ";  methods of class [[Class]] S461a "
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
                      [ ";  methods of class [[Metaclass]] 786a "
                      ,
         "(method new () (self error: 'a-metaclass-may-have-only-one-instance))"
                       ])
(* metaclasses for built-in classes 784c *)
fun metaSuper (CLASS { super = NONE,   ... }) = classClass
  | metaSuper (CLASS { super = SOME c, ... }) = metaclass c
(* type declarations for consistency checking *)
val _ = op metaSuper : class -> class
(* metaclasses for built-in classes 784d *)
fun mkMeta c methods =
  mkClass ("class " ^ className c) (META metaclassClass) (metaSuper c) []
                                                                         methods
(* type declarations for consistency checking *)
val _ = op mkMeta : class -> method list -> class
(* metaclasses for built-in classes 786b *)
fun patchMeta c = setMeta (c, mkMeta c [])
val () = app patchMeta [objectClass, nilClass, classClass, metaclassClass]
(* definition of [[newClassObject]] and supporting functions 784a *)
fun newClassObject {name, super, ivars, methods} xi =
  let val (superMeta, super) = findClass (super, xi)
        handle NotFound s => raise RuntimeError ("Superclass " ^ s ^
                                                                   " not found")
      val (cmethods, imethods) = methodDefns (superMeta, super) methods
      val class = mkClass name PENDING super ivars imethods
      val ()    = setMeta (class, mkMeta class cmethods)
  in  classObject class
  end
(* functions for managing and printing a \usmalltalk\ stack trace S494a *)
local
  (* private state and functions for printing indented traces ((usm)) S494b *)
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
  (* type declarations for consistency checking *)
  val _ = op traceMe : value ref env -> bool
  (* private state and functions for printing indented traces ((usm)) S494c *)
  val tindent = ref 0
  fun indent 0 = ()
    | indent n = (xprint "  "; indent (n-1))
  (* private state and functions for printing indented traces ((usm)) S494d *)
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

(* private state and functions for maintaining a stack of source-code locations ((usm)) S495 *)
  val locationStack = ref [] : (string * srcloc) list ref
  fun push srcloc = locationStack := srcloc :: !locationStack
  fun pop () = case !locationStack
                 of []     => raise InternalError "tracing stack underflows"
                  | h :: t => locationStack := t
in
  (* exposed tracing functions ((usm)) S497 *)
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
  (* type declarations for consistency checking *)
  val _ = op resetTrace     : unit -> unit
  val _ = op traceIndent    : string * srcloc -> value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op outdentTrace   :                    value ref env -> (unit ->
                                                            string list) -> unit
  val _ = op showStackTrace : bool -> unit
  val _ = op eprintlnTrace  : string -> unit
end
(* definition of [[primitives]] S478d *)
val primitives = (* primitives for \usmalltalk\ [[::]] S460b *)
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
                 (* primitives for \usmalltalk\ [[::]] S461b *)
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
                 (* primitives for \usmalltalk\ [[::]] S462a *)
                 ("value", valuePrim) ::
                 (* primitives for \usmalltalk\ [[::]] S480b *)
                 ("addWithOverflow", withOverflow op + ) ::
                 ("subWithOverflow", withOverflow op - ) ::
                 ("mulWithOverflow", withOverflow op * ) ::
                 (* primitives for \usmalltalk\ [[::]] S480c *)
                 ("hash", unaryPrim (fn (_, SYM s) => mkInteger (fnvHash s)
                                      | v => raise RuntimeError
                                          "hash primitive expects a symbol")) ::
                 (* primitives for \usmalltalk\ [[::]] S482c *)
                 ("newSmallInteger",   binaryPrim newInteger) ::
                 ("+",   arithop op +  )  ::
                 ("-",   arithop op -  )  ::
                 ("*",   arithop op *  )  ::
                 ("div", arithop op div)  ::
                 ("<",   intcompare op <) ::
                 (">",   intcompare op >) ::
                 ("printSmallInteger", unaryPrim printInt) ::     
                 ("printu",            unaryPrim printu)   ::     
                 (* primitives for \usmalltalk\ [[::]] S482f *)
                 ("printSymbol", unaryPrim  printSymbol) ::
                 ("newSymbol",   binaryPrim newSymbol  ) ::
                 (* primitives for \usmalltalk\ [[::]] S483e *)
                 ("arrayNew",    binaryPrim     newArray)   ::
                 ("arraySize",   arrayPrimitive arraySize)  ::
                 ("arrayAt",     arrayPrimitive arrayAt)    ::
                 ("arrayUpdate", arrayPrimitive arrayUpdate) :: nil
val () =   if isSome (OS.Process.getEnv "USMPRIM") then      (*OMIT*)
           app (println o fst) primitives else ()   (*OMIT*)
(* helper functions for evaluation 778b *)
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
(* type declarations for consistency checking *)
val _ = op findMethod : name * class -> method
val _ = op fm         : class        -> method
  in  fm class
  end
(* helper functions for evaluation S475c *)
fun optimizedBind (x, v, xi) =
  let val loc = find (x, xi)
  in  (loc := v; xi)
  end handle NotFound _ => bind (x, ref v, xi)
(* definition of the [[Return]] exception 775a *)
exception Return of { value : value, to : frame, unwound : active_send list }
(* definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk 776b *)
fun eval (e, rho, superclass, F, xi) =
  let val go = applyCheckingOverflow id in go end (* OMIT *)
  let (* definition of function [[evalMethod]] 778a *)
      fun evalMethod ({ name, superclass, formals, locals, body }, receiver, vs,
                                                                         Fhat) =
            let val ivars  = instanceVars receiver
                val args   = mkEnv (formals, map ref vs)
                val locals = mkEnv (locals,  map (fn _ => ref nilValue) locals)
            in  eval (body, ivars <+> args <+> locals, superclass, Fhat, xi)
            end
            handle BindListLength => raise InternalError
                                             "bad arity in user method" (*OMIT*)
      (* type declarations for consistency checking *)
      val _ = op evalMethod   : method * value * value list * frame -> value
      (* function [[ev]], the evaluator proper ((usm)) 776c *)
      fun ev (RETURN e) = raise Return { value = ev e, to = F, unwound = [] }
      (* function [[ev]], the evaluator proper ((usm)) 777 *)
        | ev (SEND (srcloc, receiver, msgname, args))  =
            let val obj as (class, rep) = ev receiver
                val vs = map ev args
                val _ = if logging then logSend srcloc msgname else () (*OMIT*)
                val startingClass = case receiver of SUPER => superclass | _ =>
                                                                           class
                val checkpoint = checkpointLimit ()  (*OMIT*)
                (* definition of function [[trace]] S486 *)
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

(* reraise [[Return]], adding [[msgname]], [[class]], and [[loc]] to [[unwound]] S478b *)
                           let val this = { method = msgname, class = className
                                                           class, loc = srcloc }
                           in  raise Return { value = v, to = F', unwound = this
                                                                    :: unwound }
                           end
                   end)
            end
      (* function [[ev]], the evaluator proper ((usm)) 779a *)
        | ev (BLOCK (formals, body)) = mkBlock (formals, body, rho, superclass,
                                                                              F)
      (* function [[ev]], the evaluator proper ((usm)) 779d *)
        | ev (VALUE v) = v
      (* function [[ev]], the evaluator proper ((usm)) 780a *)
        | ev (LITERAL c) = 
            (case c of NUM n => mkInteger n
                     | SYM s => mkSymbol s
                     | _ => raise InternalError "unexpected literal")
      (* function [[ev]], the evaluator proper ((usm)) 780b *)
        | ev (VAR x) = !(find (x, rho) handle NotFound _ => find (x, xi))
        | ev (SET (x, e)) =
            let val v = ev e
                val cell = find (x, rho) handle NotFound _ => find (x, xi)
            in  cell := v; v
            end 
      (* function [[ev]], the evaluator proper ((usm)) 780c *)
        | ev (SUPER) = ev (VAR "self")
      (* function [[ev]], the evaluator proper ((usm)) 781a *)
        | ev (BEGIN es) =
            let fun b (e::es, lastval) = b (es, ev e)
                  | b (   [], lastval) = lastval
            in  b (es, nilValue)
            end
      (* function [[ev]], the evaluator proper ((usm)) 781b *)
        | ev (PRIMITIVE (p, args)) =
            let val f = find (p, primitives)
                        handle NotFound n =>
                          raise RuntimeError ("There is no primitive named " ^ n
                                                                               )
            in  f (map ev args, xi)
            end
(* type declarations for consistency checking *)
val _ = op eval: exp * value ref env * class * frame * value ref env -> value
val _ = op ev  : exp -> value
  in  ev e
  end
(* definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk 779c *)
fun applyClosure ((formals, body, rho, superclass, frame), vs, xi) =
  eval (BEGIN body, bindList (formals, map ref vs, rho), superclass, frame, xi)
  handle BindListLength => 
      raise RuntimeError ("wrong number of arguments to block; expected " ^
                          "(<block> " ^ valueSelector formals ^ " " ^
                          spaceSep formals ^ ")")
(* type declarations for consistency checking *)
val _ = op applyClosure : closure * value list * value ref env -> value
val () = applyClosureRef := applyClosure
(* definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk 782 *)
fun evaldef (d, xi) =
  let fun ev e = eval (e, emptyEnv, objectClass, noFrame, xi)
                 handle Return { value = v, unwound = frames, ... } =>
                   (* report [[return]] escapes [[frames]] S498b *)
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
(* type declarations for consistency checking *)
val _ = op evaldef : def * value ref env -> value ref env * value
val _ = op ev      : exp -> value
  in  (xi', v)
  end
(* definitions of [[eval]], [[evaldef]], [[basis]], and [[processDef]] for \usmalltalk S487a *)
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
(* definition of [[testIsGood]] for \usmalltalk S499a *)
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

(* definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]] S499b *)
      fun whatWasExpected (LITERAL (NUM n), _) = printsAs (mkInteger n)
        | whatWasExpected (LITERAL (SYM x), _) = printsAs (mkSymbol x)
        | whatWasExpected (e, OK v) =
            concat [printsAs v, " (from evaluating ", expString e, ")"]
        | whatWasExpected (e, ERROR _) =
            concat ["the result of evaluating ", expString e]

(* definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]] S500a *)
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

(* definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]] S500b *)
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

(* definitions of [[check{Expect,Assert,Error}Passes]] that call [[printsAs]] S500c *)
      val cefailed = "check-error failed: "
      fun checkErrorPasses checkx =
            case outcome checkx
              of ERROR _ => true
               | OK check =>
                   failtest [cefailed, "expected evaluating ", expString checkx,
                             " to cause an error, but evaluation produced ",
                             printsAs check]
      (* definition of [[checkPrintPasses]] S500d *)

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
(*   IMPLEMENTATIONS OF \USMALLTALK\ PRIMITIVES AND DEFINITION OF [[INITIALBASIS]] *)
(*                                                               *)
(*****************************************************************)

(* implementations of \usmalltalk\ primitives and definition of [[initialBasis]] S487c *)
val initialXi = emptyEnv

fun addClass (c, xi) = bind (className c, ref (classObject c), xi)
val initialXi =
  foldl addClass initialXi [ objectClass, nilClass, classClass, metaclassClass ]
(* implementations of \usmalltalk\ primitives and definition of [[initialBasis]] S488a *)
val initialXi =
  let val xdefs =
        stringsxdefs ("predefined classes", 
                      
                       [ ";  predefined uSmalltalk classes and values 743 "
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
                       , ";  predefined uSmalltalk classes and values 744a "
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
                       , ";  predefined uSmalltalk classes and values S461d "
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
                       , ";  predefined uSmalltalk classes and values S483a "
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
                       , ";  predefined uSmalltalk classes and values S485d "
                       , "(class CompiledMethod"
                       , "  [subclass-of Object]"
                       , ")"
                       , ";  predefined uSmalltalk classes and values S488d "
                       , ";  numeric classes 744b "
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
                       ,
";  numeric classes ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) "
                       , ";  definition of class [[Number]] S465a "
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
                       , ";      other methods of class [[Number]] 756b "
                       , "    (method -   (y) (self + (y  negated)))"
                       ,
"    (method abs ()  ((self isNegative) ifTrue:ifFalse: {(self  negated)} {self}))"
                       , "    (method /   (y) (self * (y reciprocal)))"
                       , ";      other methods of class [[Number]] 757a "
                       ,
                 "    (method isNegative         () (self  < (self coerce: 0)))"
                       ,
                 "    (method isNonnegative      () (self >= (self coerce: 0)))"
                       ,
                 "    (method isStrictlyPositive () (self  > (self coerce: 0)))"
                       , ";      other methods of class [[Number]] S465b "
                       , "    (method squared () (self * self))"
                       , "    (method raisedToInteger: (anInteger)"
                       , "        ((anInteger = 0) ifTrue:ifFalse:"
                       , "            {(self coerce: 1)}"
                       , "            {((anInteger = 1) ifTrue:ifFalse: {self}"
                       ,
      "                {(((self raisedToInteger: (anInteger div: 2)) squared) *"
                       ,
          "                    (self raisedToInteger: (anInteger mod: 2)))})}))"
                       , ";      other methods of class [[Number]] S465c "
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
                       , ";  numeric classes 758a "
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
                       , ";      other methods of class [[Fraction]] 758b "
                       , "    (method num () num)  ; private"
                       , "    (method den () den)  ; private"
                       , ";      other methods of class [[Fraction]] 758c "
                       ,
                   "    (method = (f) ((num = (f num)) and: {(den = (f den))}))"
                       ,
                        "    (method < (f) ((num * (f den)) < ((f num) * den)))"
                       , ";      other methods of class [[Fraction]] 759a "
                       , "    (method * (f)"
                       ,
"        (((Fraction new) setNum:den: (num * (f num)) (den * (f den))) divReduce))"
                       , ";      other methods of class [[Fraction]] 759b "
                       , "    (method + (f) [locals temp]"
                       , "        (set temp (den lcm: (f den)))"
                       , "        (((Fraction new) setNum:den:"
                       ,
"                         ((num * (temp div: den)) + ((f num) * (temp div: (f den))))"
                       , "                         temp)"
                       , "            divReduce))"
                       , ";      other methods of class [[Fraction]] 759c "
                       , "    (method isNegative         () (num isNegative))"
                       ,
                        "    (method isNonnegative      () (num isNonnegative))"
                       ,
                   "    (method isStrictlyPositive () (num isStrictlyPositive))"
                       , ";      other methods of class [[Fraction]] S467a "
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
                       , ";      other methods of class [[Fraction]] S467b "
                       ,
        "    (method negated () ((Fraction new) setNum:den: (num negated) den))"
                       , ";      other methods of class [[Fraction]] S467c "
                       , "    (method reciprocal ()"
                       ,
                     "       (((Fraction new) setNum:den: den num) signReduce))"
                       , ";      other methods of class [[Fraction]] S467d "
                       ,
                 "    (method print () (num print) ('/ print) (den print) self)"
                       , ";      other methods of class [[Fraction]] S468a "
                       , "    (method asInteger  () (num div: den))"
                       ,
                    "    (method asFloat    () ((num asFloat) / (den asFloat)))"
                       , "    (method asFraction () self)"
                       , "    (method coerce: (aNumber) (aNumber asFraction))"
                       , ")"
                       , ";  numeric classes 760 "
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
                       , ";  numeric classes S466a "
                       , "(class Integer"
                       , "    [subclass-of Number] ; abstract class"
                       , "    (method div: (n) (self subclassResponsibility))"
                       , "    (method mod: (n) (self - (n * (self div: n))))"
                       ,
"    (method gcd: (n) ((n = (self coerce: 0)) ifTrue:ifFalse: {self} {(n gcd: (self mod: n))}))"
                       , "    (method lcm: (n) (self * (n div: (self gcd: n))))"
                       , ";      other methods of class [[Integer]] 757b "
                       ,
                        "    (method asFraction () (Fraction  num:den: self 1))"
                       ,
                        "    (method asFloat    () (Float mant:exp:    self 0))"
                       , "    (method asInteger  () self)"
                       , ";      other methods of class [[Integer]] 757c "
                       , "    (method coerce: (aNumber) (aNumber asInteger))"
                       , ";      other methods of class [[Integer]] 757d "
                       ,
                        "    (method reciprocal () (Fraction num:den: 1 self)) "
                       ,
                        "    (method / (aNumber) ((self asFraction) / aNumber))"
                       , ";      other methods of class [[Integer]] S466b "
                       , "    (method timesRepeat: (aBlock) [locals count]"
                       ,
    "        ((self isNegative) ifTrue: {(self error: 'negative-repeat-count)})"
                       , "        (set count self)"
                       , "        ({(count != 0)} whileTrue:"
                       , "             {(aBlock value)"
                       , "              (set count (count - 1))}))"
                       , ")"
                       , ";  numeric classes S466c "
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
                       , ";  numeric classes S468b "
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
                       , ";      other methods of class [[Float]] S469a "
                       , "    (method mant () mant)  ; private"
                       , "    (method exp  () exp)   ; private"
                       , ";      other methods of class [[Float]] S469b "
                       , "    (method < (x) ((self - x) isNegative))"
                       , "    (method = (x) ((self - x)   isZero))"
                       , "    (method isZero () (mant = 0))  ; private"
                       , ";      other methods of class [[Float]] S469c "
                       ,
                  "    (method negated () (Float mant:exp: (mant negated) exp))"
                       , ";      other methods of class [[Float]] S469d "
                       , "    (method + (x-prime) "
                       , "        ((exp >= (x-prime exp)) ifTrue:ifFalse:"
                       ,
"            {(Float mant:exp: ((mant * (10 raisedToInteger: (exp - (x-prime exp)))) +"
                       , "                                 (x-prime mant))"
                       , "                              (x-prime exp))}"
                       , "            {(x-prime + self)}))"
                       , ";      other methods of class [[Float]] S469e "
                       , "    (method * (x-prime) "
                       ,
      "        (Float mant:exp: (mant * (x-prime mant)) (exp + (x-prime exp))))"
                       , ";      other methods of class [[Float]] S469f "
                       , "    (method reciprocal ()"
                       ,
                  "        (Float mant:exp: (1000000000 div: mant) (-9 - exp)))"
                       , ";      other methods of class [[Float]] S470a "
                       , "    (method coerce: (aNumber) (aNumber asFloat))"
                       , "    (method asFloat () self)"
                       , ";      other methods of class [[Float]] S470b "
                       , "    (method asInteger ()"
                       , "        ((exp isNegative) ifTrue:ifFalse:"
                       ,
                 "            {(mant div: (10 raisedToInteger: (exp negated)))}"
                       , "            {(mant    * (10 raisedToInteger: exp))}))"
                       , ";      other methods of class [[Float]] S470c "
                       , "    (method asFraction ()"
                       , "        ((exp < 0) ifTrue:ifFalse:"
                       ,
    "            {(Fraction num:den: mant (10 raisedToInteger: (exp negated)))}"
                       ,
      "            {(Fraction num:den: (mant * (10 raisedToInteger: exp)) 1)}))"
                       , ";      other methods of class [[Float]] S470d "
                       , "    (method isNegative         () (mant isNegative))"
                       ,
                       "    (method isNonnegative      () (mant isNonnegative))"
                       ,
                  "    (method isStrictlyPositive () (mant isStrictlyPositive))"
                       , ";      other methods of class [[Float]] S470e "
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
                       ,
  ";  predefined uSmalltalk classes and values that use numeric literals S462b "
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
                       ,
  ";  predefined uSmalltalk classes and values that use numeric literals S462c "
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
                       , ";  collection classes 745a "
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
                       , ";    other methods of class [[Collection]] 745b "
                       , "  (class-method with: (anObject)"
                       , "      ((self new) add: anObject))"
                       , ";    other methods of class [[Collection]] 745c "
                       , "  (class-method withAll: (aCollection)"
                       , "      ((self new) addAll: aCollection))"
                       , ";    other methods of class [[Collection]] 745d "
                       , "  (method remove: (oldObject) "
                       ,
"      (self remove:ifAbsent: oldObject {(self error: 'tried-to-remove-absent-object)}))"
                       , "  (method addAll: (aCollection) "
                       , "      (aCollection do: [block (x) (self add: x)])"
                       , "      self)"
                       , "  (method removeAll: (aCollection) "
                       , "      (aCollection do: [block (x) (self remove: x)])"
                       , "      self)"
                       , ";    other methods of class [[Collection]] 746a "
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
                       , ";    other methods of class [[Collection]] 746b "
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
                       , ";    other methods of class [[Collection]] 746c "
                       , "  (method inject:into: (thisValue binaryBlock)"
                       ,
"     (self do: [block (x) (set thisValue (binaryBlock value:value: x thisValue))])"
                       , "     thisValue)"
                       , ";    other methods of class [[Collection]] 747a "
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
                       , ";    other methods of class [[Collection]] 747b "
                       , "  (method species () (self class))"
                       , ";    other methods of class [[Collection]] 747c "
                       , "  (method print ()"
                       , "      (self printName)"
                       , "      (left-round print)"
                       , "      (self do: [block (x) (space print) (x print)])"
                       , "      (space print)"
                       , "      (right-round print)"
                       , "      self)"
                       , "  (method printName () (((self class) name) print))"
                       , ")"
                       , ";  collection classes 748a "
                       , "(class KeyedCollection"
                       , "    [subclass-of Collection]  ; abstract class"
                       ,
 "    (method at:put: (key value)                (self subclassResponsibility))"
                       ,
 "    (method associationsDo: (aBlock)           (self subclassResponsibility))"
                       ,
 "    (method removeKey:ifAbsent: (key exnBlock) (self subclassResponsibility))"
                       ,
                       ";      other methods of class [[KeyedCollection]] 748b "
                       , "    (method do: (aBlock) "
                       ,
"        (self associationsDo: [block (anAssoc) (aBlock value: (anAssoc value))]))"
                       ,
                       ";      other methods of class [[KeyedCollection]] 748c "
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
                       ,
                       ";      other methods of class [[KeyedCollection]] 749a "
                       , "    (method keyAtValue: (value) "
                       ,
   "        (self keyAtValue:ifAbsent: value {(self error: 'value-not-found)}))"
                       , "    (method keyAtValue:ifAbsent: (value exnBlock)"
                       , "        (self associationsDo: [block (x) "
                       ,
                "            (((x value) = value) ifTrue: {(return (x key))})])"
                       , "        (exnBlock value))"
                       ,
                       ";      other methods of class [[KeyedCollection]] 749b "
                       , "    (method removeKey: (key)    "
                       ,
        "        (self removeKey:ifAbsent: key {(self error: 'key-not-found)}))"
                       ,
                       ";      other methods of class [[KeyedCollection]] 749c "
                       , "    (method = (collection)"
                       , "        (self associationsDo:"
                       , "            [block (assn)"
                       , "                 (((assn value) = "
                       ,
"                              (collection at:ifAbsent: (assn key) {(return false)})) ifFalse:"
                       , "                           {(return false)})])"
                       , "        ((self size) = (collection size)))"
                       , ")"
                       , ";  collection classes 750 "
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
                       , ";  collection classes 752a "
                       , ";  classes that define cons cells and sentinels 753a "
                       , "(class Cons"
                       , "    [subclass-of Object]"
                       , "    [ivars car cdr]"
                       , "    (method car ()           car)"
                       , "    (method cdr ()           cdr)"
                       , "    (method car: (anObject)  (set car anObject) self)"
                       , "    (method cdr: (anObject)  (set cdr anObject) self)"
                       , "    (method pred: (aCons)    nil)"
                       , ";      more methods of class [[Cons]] 753b "
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
                       , ";      more methods of class [[Cons]] 753c "
                       , "    (method do: (aBlock)"
                       , "        (aBlock value: car)"
                       , "        (cdr do: aBlock))"
                       , ";      more methods of class [[Cons]] 754a "
                       ,
               "    (method rejectOne:ifAbsent:withPred: (aBlock exnBlock pred)"
                       , "        ((aBlock value: self) ifTrue:ifFalse:"
                       , "            {(pred deleteAfter)}"
                       ,
       "            {(cdr rejectOne:ifAbsent:withPred: aBlock exnBlock self)}))"
                       , ")"
                       , ";  classes that define cons cells and sentinels 754c "
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
                      ";      iterating methods of class [[ListSentinel]] 753d "
                       , "    (method do: (aBlock) nil)"
                       ,
                      ";      iterating methods of class [[ListSentinel]] 754b "
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
                       , ";      other methods of class [[List]] 752b "
                       ,
      "    (method addLast:  (item)   ((sentinel pred) insertAfter: item) self)"
                       ,
      "    (method addFirst: (item)   (sentinel insertAfter: item)        self)"
                       , "    (method add:      (item)   (self addLast: item))"
                       , ";      other methods of class [[List]] 752c "
                       ,
                        "    (method removeFirst ()     (sentinel deleteAfter))"
                       , "    (method removeLast  ()     (self leftAsExercise))"
                       , ";      other methods of class [[List]] 752d "
                       , "    (method remove:ifAbsent: (oldObject exnBlock)"
                       , "        ((sentinel cdr)"
                       , "            rejectOne:ifAbsent:withPred:"
                       , "            [block (x) (oldObject = (x car))]"
                       , "            exnBlock"
                       , "            sentinel))"
                       , ";      other methods of class [[List]] 752e "
                       ,
           "    (method removeKey:ifAbsent: (n exnBlock) (self leftAsExercise))"
                       , ";      other methods of class [[List]] 752f "
                       , "    (method firstKey () 0)"
                       , "    (method lastKey  () ((self size) - 1))"
                       , "    (method at:put: (n value) [locals tmp]"
                       , "        (set tmp (sentinel cdr))"
                       , "        ({(n = 0)} whileFalse:"
                       , "           {(set n (n - 1))"
                       , "            (set tmp (tmp cdr))})"
                       , "        (tmp car: value)"
                       , "        self)"
                       , ")"
                       , ";  collection classes S462d "
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
                       , ";  collection classes S463a "
                       , "(class Dictionary"
                       , "    [subclass-of KeyedCollection]"
                       , "    [ivars table] ; list of Associations"
                       ,
                   "    (class-method new ()      ((super new) initDictionary))"
                       ,
          "    (method initDictionary () (set table (List new)) self) ; private"
                       , ";      other methods of class [[Dictionary]] S463b "
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
                       , ";      other methods of class [[Dictionary]] S463c "
                       , "    (method removeKey:ifAbsent: (key exnBlock)"
                       ,
                     "       [locals value-removed] ; value found if not absent"
                       ,
"       (set value-removed (self at:ifAbsent: key {(return (exnBlock value))}))"
                       ,
"       (set table (table reject: [block (assn) (key = (assn key))])) ; remove assoc"
                       , "       value-removed)"
                       , ";      other methods of class [[Dictionary]] S463d "
                       , "    (method remove:ifAbsent: (value exnBlock)"
                       ,
                "       (self error: 'Dictionary-uses-remove:key:-not-remove:))"
                       , ";      other methods of class [[Dictionary]] S463e "
                       , "    (method add: (anAssociation)"
                       ,
               "      (self at:put: (anAssociation key) (anAssociation value)))"
                       , ";      other methods of class [[Dictionary]] S464a "
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
                       , ";  collection classes S464b "
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
                       , ";      other methods of class [[Array]] 754d "
                       ,
                  "    (method add:                (x)   (self fixedSizeError))"
                       ,
                  "    (method remove:ifAbsent:    (x b) (self fixedSizeError))"
                       ,
                  "    (method removeKey:ifAbsent: (x b) (self fixedSizeError))"
                       ,
  "    (method fixedSizeError      ()    (self error: 'arrays-have-fixed-size))"
                       , ";      other methods of class [[Array]] 754e "
                       , "    (method firstKey () 0)"
                       , "    (method lastKey  () ((self size) - 1))"
                       , "    (method do: (aBlock) [locals index]"
                       , "        (set index (self firstKey))"
                       , "        ((self size) timesRepeat:"
                       , "           {(aBlock value: (self at: index))"
                       , "            (set index (index + 1))}))"
                       ,
                  ";      other methods of class [[Array]] ((prototype)) S464c "
                       ,
    "    (method select:  (_) (self error: 'select-on-arrays-left-as-exercise))"
                       ,
   "    (method collect: (_) (self error: 'collect-on-arrays-left-as-exercise))"
                       , ")"
                       , ";  collection classes S471 "
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
(* implementations of \usmalltalk\ primitives and definition of [[initialBasis]] S488b *)
local 
  fun newInstance classname = SEND (nullsrc, VAR classname, "new", [])
in
  val initialXi = processPredefined (VAL ("true",  newInstance "True" ),
                                                                      initialXi)
  val initialXi = processPredefined (VAL ("false", newInstance "False"),
                                                                      initialXi)
end
(* implementations of \usmalltalk\ primitives and definition of [[initialBasis]] S488c *)
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
(* implementations of \usmalltalk\ primitives and definition of [[initialBasis]] S488e *)
val initialXi = processPredefined (VAL ("nil", VALUE nilValue), initialXi)
val initialBasis = initialXi


(*****************************************************************)
(*                                                               *)
(*   FUNCTION [[RUNAS]] FOR \USMALLTALK, WHICH PRINTS STACK TRACES *)
(*                                                               *)
(*****************************************************************)

(* function [[runAs]] for \usmalltalk, which prints stack traces S498d *)
fun runAs interactivity = 
  let val _ = setup_error_format interactivity
      val prompts = if prompts interactivity then stdPrompts else noPrompts
      val xdefs = filexdefs ("standard input", TextIO.stdIn, prompts)
  in  ignore (readEvalPrintWith eprintlnTrace (xdefs, initialBasis,
                                                                 interactivity))
  end 
(* type declarations for consistency checking *)
val _ = op runAs : interactivity -> unit
fun dump_global_names () = app (println o fst) initialBasis  (*OMIT*)


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


(*****************************************************************)
(*                                                               *)
(*   TYPE ASSERTIONS FOR \USMALLTALK                             *)
(*                                                               *)
(*****************************************************************)

(* type assertions for \usmalltalk ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
(* type declarations for consistency checking *)
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
(* type assertions for \usmalltalk ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) *)
(* type declarations for consistency checking *)
val _ = mkBlock : name list * exp list * value ref env * class * frame -> value
val _ = saveBlockClass : value ref env -> unit
