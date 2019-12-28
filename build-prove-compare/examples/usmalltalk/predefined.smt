;;;usm.nw:4602
(class Boolean 
    [subclass-of Object]
    (method ifTrue:ifFalse: (trueBlock falseBlock) (self subclassResponsibility))
  
    (method ifFalse:ifTrue: (falseBlock trueBlock) 
        (self ifTrue:ifFalse: trueBlock falseBlock))
    (method ifTrue:  (trueBlock)  (self ifTrue:ifFalse: trueBlock {}))
    (method ifFalse: (falseBlock) (self ifTrue:ifFalse: {} falseBlock))
    
    (method not ()          (self ifTrue:ifFalse: {false}          {true}))
    (method eqv: (aBoolean) (self ifTrue:ifFalse: {aBoolean}       {(aBoolean not)}))
    (method xor: (aBoolean) (self ifTrue:ifFalse: {(aBoolean not)} {aBoolean}))

    (method & (aBoolean) (self ifTrue:ifFalse: {aBoolean} {self}))
    (method | (aBoolean) (self ifTrue:ifFalse: {self} {aBoolean}))
  
    (method and: (alternativeBlock) (self ifTrue:ifFalse: alternativeBlock {self}))
    (method or:  (alternativeBlock) (self ifTrue:ifFalse: {self} alternativeBlock))
)
;;;usm.nw:4644
(class True 
  [subclass-of Boolean]
  (method ifTrue:ifFalse: (trueBlock falseBlock) (trueBlock value))
)
(class False
  [subclass-of Boolean]
  (method ifTrue:ifFalse: (trueBlock falseBlock) (falseBlock value))
)
;;;usma.nw:2016
(class Block
    [subclass-of Object] ; internal representation
    (class-method new () {})
    (method value                    ()            (primitive value self))
    (method value:                   (a1)          (primitive value self a1))
    (method value:value:             (a1 a2)       (primitive value self a1 a2))
    (method value:value:value:       (a1 a2 a3)    (primitive value self a1 a2 a3))
    (method value:value:value:value: (a1 a2 a3 a4) (primitive value self a1 a2 a3 a4))
    (method whileTrue: (body)
        ((self value) ifTrue:ifFalse:
            {(body value)
             (self whileTrue: body)}
            {nil}))
    (method whileFalse: (body) 
         ((self value) ifTrue:ifFalse:
             {nil}
             {(body value) 
              (self whileFalse: body)}))
)
;;;usma.nw:3912
(class Symbol
    [subclass-of Object] ; internal representation
    (class-method new  () (self error: 'can't-send-new-to-Symbol))
    (class-method new: (aSymbol) (primitive newSymbol self aSymbol))
    (method       print  () (primitive printSymbol self))
    (method       hash   () (primitive hash self))
)
;;;usma.nw:4062
(class CompiledMethod
  [subclass-of Object]
)
;;;usm.nw:4803
(class Magnitude
    [subclass-of Object] ; abstract class
    (method =  (x) (self subclassResponsibility)) ; may not inherit from Object
    (method <  (x) (self subclassResponsibility))
    (method >  (y) (y < self))
    (method <= (x) ((self > x) not))
    (method >= (x) ((self < x) not))
    (method min: (aMagnitude) ((self < aMagnitude) ifTrue:ifFalse: {self} {aMagnitude}))
    (method max: (aMagnitude) ((self > aMagnitude) ifTrue:ifFalse: {self} {aMagnitude}))
)
;;;usma.nw:2388
(class Number
    [subclass-of Magnitude]  ; abstract class
    ;;;;;;; basic Number protocol
    (method +   (aNumber)     (self subclassResponsibility))
    (method *   (aNumber)     (self subclassResponsibility))
    (method negated    ()     (self subclassResponsibility))
    (method reciprocal ()     (self subclassResponsibility))
    
    (method asInteger  ()     (self subclassResponsibility))
    (method asFraction ()     (self subclassResponsibility))
    (method asFloat    ()     (self subclassResponsibility))
    (method coerce: (aNumber) (self subclassResponsibility))
    
;;;usm.nw:5923
(method -   (y) (self + (y  negated)))
(method abs ()  ((self isNegative) ifTrue:ifFalse: {(self  negated)} {self}))
(method /   (y) (self * (y reciprocal)))
;;;usm.nw:5933
(method isNegative         () (self  < (self coerce: 0)))
(method isNonnegative      () (self >= (self coerce: 0)))
(method isStrictlyPositive () (self  > (self coerce: 0)))
;;;usma.nw:2410
(method squared () (self * self))
(method raisedToInteger: (anInteger)
    ((anInteger = 0) ifTrue:ifFalse:
        {(self coerce: 1)}
        {((anInteger = 1) ifTrue:ifFalse: {self}
            {(((self raisedToInteger: (anInteger div: 2)) squared) *
                (self raisedToInteger: (anInteger mod: 2)))})}))
;;;usma.nw:2439
(method sqrt () (self sqrtWithin: (self coerce: (1 / 1000))))
(method sqrtWithin: (epsilon) [locals two x<i-1> x<i>]
    ; find square root of receiver within epsilon
    (set two    (self coerce: 2))
    (set x<i-1> (self coerce: 1))
    (set x<i>   ((x<i-1> + (self / x<i-1>)) / two))
    ({(((x<i-1> - x<i>) abs) > epsilon)} whileTrue:
           {(set x<i-1> x<i>)
            (set x<i> ((x<i-1> + (self / x<i-1>)) / two))})
    x<i>)
;;;usma.nw:2401
)
;;;usm.nw:6034
(class Fraction
    [subclass-of Number]
    [ivars num den]
    (class-method num:den: (a b) ((self new) initNum:den: a b))
    (method initNum:den: (a b) ; private
        (self setNum:den: a b)
        (self signReduce)
        (self divReduce))
    (method setNum:den: (a b) (set num a) (set den b) self) ; private
    
;;;usm.nw:6070
(method num () num)  ; private
(method den () den)  ; private
;;;usm.nw:6087
(method = (f) ((num = (f num)) and: {(den = (f den))}))
(method < (f) ((num * (f den)) < ((f num) * den)))
;;;usm.nw:6103
(method * (f)
    (((Fraction new) setNum:den: (num * (f num)) (den * (f den))) divReduce))
;;;usm.nw:6120
(method + (f) [locals temp]
    (set temp (den lcm: (f den)))
    (((Fraction new) setNum:den:
                     ((num * (temp div: den)) + ((f num) * (temp div: (f den))))
                     temp)
        divReduce))
;;;usm.nw:6134
(method isNegative         () (num isNegative))
(method isNonnegative      () (num isNonnegative))
(method isStrictlyPositive () (num isStrictlyPositive))
;;;usma.nw:2868
(method signReduce () ; private
    ((den isNegative) ifTrue:
        {(set num (num negated)) (set den (den negated))})
    self)

(method divReduce () [locals temp] ; private
    ((num = 0) ifTrue:ifFalse:
        {(set den 1)}
        {(set temp ((num abs) gcd: den))
         (set num  (num div: temp))
         (set den  (den div: temp))})
    self)
;;;usma.nw:2890
(method negated () ((Fraction new) setNum:den: (num negated) den))
;;;usma.nw:2909
(method reciprocal ()
   (((Fraction new) setNum:den: den num) signReduce))
;;;usma.nw:2914
(method print () (num print) ('/ print) (den print) self)
;;;usma.nw:2924
(method asInteger  () (num div: den))
(method asFloat    () ((num asFloat) / (den asFloat)))
(method asFraction () self)
(method coerce: (aNumber) (aNumber asFraction))
;;;usm.nw:6044
)
;;;usm.nw:6431
(class Natural
   [subclass-of Magnitude]
   ; instance variables left as an exercise

   (class-method fromSmall: (anInteger) (self leftAsExercise))

   (method = (aNatural) (self leftAsExercise))
   (method < (aNatural) (self leftAsExercise))

   (method + (aNatural) (self leftAsExercise))
   (method * (aNatural) (self leftAsExercise))
   (method - (aNatural) (self subtract:withDifference:ifNegative aNatural
                          {(self error: 'Natural-subtraction-went-negative)}))
   (method subtract:withDifference:ifNegative (aNatural exnBlock)
                        (self leftAsExercise))

   (method sdiv: (n) (self sdivmod:with: n [block (q r) q]))
   (method smod: (n) (self sdivmod:with: n [block (q r) r]))
   (method sdivmod:with: (n aBlock) (self leftAsExercise))

   (method decimal () (self leftAsExercise))
   (method isZero  () (self leftAsExercise))

   (method print   () ((self decimal) do: [block (x) (x print)]))
)
;;;usma.nw:2778
(class Integer
    [subclass-of Number] ; abstract class
    (method div: (n) (self subclassResponsibility))
    (method mod: (n) (self - (n * (self div: n))))
    (method gcd: (n) ((n = (self coerce: 0)) ifTrue:ifFalse: {self} {(n gcd: (self mod: n))}))
    (method lcm: (n) (self * (n div: (self gcd: n))))
    
;;;usm.nw:5965
(method asFraction () (Fraction  num:den: self 1))
(method asFloat    () (Float mant:exp:    self 0))
(method asInteger  () self)
;;;usm.nw:5974
(method coerce: (aNumber) (aNumber asInteger))
;;;usm.nw:5982
(method reciprocal () (Fraction num:den: 1 self)) 
(method / (aNumber) ((self asFraction) / aNumber))
;;;usma.nw:2798
(method timesRepeat: (aBlock) [locals count]
    ((self isNegative) ifTrue: {(self error: 'negative-repeat-count)})
    (set count self)
    ({(count != 0)} whileTrue:
         {(aBlock value)
          (set count (count - 1))}))
;;;usma.nw:2785
)
;;;usma.nw:2826
(class SmallInteger
    [subclass-of Integer] ; primitive representation
    (class-method new: (n) (primitive newSmallInteger self n))
    (class-method new  ()  (self new: 0))
    (method negated    ()  (0 - self))
    (method print      ()  (primitive printSmallInteger self))
    (method +          (n) (primitive + self n))
    (method -          (n) (primitive - self n))
    (method *          (n) (primitive * self n))
    (method div:       (n) (primitive div self n))
    (method =          (n) (primitive sameObject self n))
    (method <          (n) (primitive < self n))
    (method >          (n) (primitive > self n))
)
;;;usma.nw:2987
(class Float
    [subclass-of Number]
    [ivars mant exp]
    (class-method mant:exp: (m e) ((self new) initMant:exp: m e))
    (method initMant:exp: (m e) ; private
        (set mant m) (set exp e) (self normalize))
    (method normalize ()    ; private
        ({((mant abs) > 32767)} whileTrue:
               {(set mant (mant div: 10))
                (set exp (exp + 1))})
        self)
    
;;;usma.nw:3004
(method mant () mant)  ; private
(method exp  () exp)   ; private
;;;usma.nw:3012
(method < (x) ((self - x) isNegative))
(method = (x) ((self - x)   isZero))
(method isZero () (mant = 0))  ; private
;;;usma.nw:3019
(method negated () (Float mant:exp: (mant negated) exp))
;;;usma.nw:3044
(method + (x-prime) 
    ((exp >= (x-prime exp)) ifTrue:ifFalse:
        {(Float mant:exp: ((mant * (10 raisedToInteger: (exp - (x-prime exp)))) +
                             (x-prime mant))
                          (x-prime exp))}
        {(x-prime + self)}))
;;;usma.nw:3057
(method * (x-prime) 
    (Float mant:exp: (mant * (x-prime mant)) (exp + (x-prime exp))))
;;;usma.nw:3066
(method reciprocal ()
    (Float mant:exp: (1000000000 div: mant) (-9 - exp)))
;;;usma.nw:3072
(method coerce: (aNumber) (aNumber asFloat))
(method asFloat () self)
;;;usma.nw:3078
(method asInteger ()
    ((exp isNegative) ifTrue:ifFalse:
        {(mant div: (10 raisedToInteger: (exp negated)))}
        {(mant    * (10 raisedToInteger: exp))}))
;;;usma.nw:3086
(method asFraction ()
    ((exp < 0) ifTrue:ifFalse:
        {(Fraction num:den: mant (10 raisedToInteger: (exp negated)))}
        {(Fraction num:den: (mant * (10 raisedToInteger: exp)) 1)}))
;;;usma.nw:3112
(method isNegative         () (mant isNegative))
(method isNonnegative      () (mant isNonnegative))
(method isStrictlyPositive () (mant isStrictlyPositive))
;;;usma.nw:3131
(method print () 
    (self print-normalize) 
    (mant print) ('x10^ print) (exp print)
    (self normalize))

(method print-normalize ()
    ({((exp < 0) and: {((mant mod: 10) = 0)})} whileTrue:
        {(set exp (exp + 1)) (set mant (mant div: 10))}))
;;;usma.nw:2999
)
;;;usma.nw:2086
(class Char
   [subclass-of Object]
   [ivars code-point]
   (class-method new: (n) ((self new) init: n))
   (method init:      (n) (set code-point n) self) ;; private
   (method print      ()  (primitive printu code-point))
   (method =          (c) (code-point = (c code-point)))
   (method code-point ()  code-point) ;; private
)
;;;usma.nw:2106
(val newline      (Char new: 10))   (val left-round   (Char new:  40))
(val space        (Char new: 32))   (val right-round  (Char new:  41))
(val semicolon    (Char new: 59))   (val left-curly   (Char new: 123))
(val quote        (Char new: 39))   (val right-curly  (Char new: 125))
                                    (val left-square  (Char new:  91))
                                    (val right-square (Char new:  93))
;;;usm.nw:4862
(class Collection
  [subclass-of Object] ; abstract
  (method do:     (aBlock)       (self subclassResponsibility))
  (method add:    (newObject)    (self subclassResponsibility))
  (method remove:ifAbsent: (oldObject exnBlock)
                                 (self subclassResponsibility))
  (method =       (aCollection)  (self subclassResponsibility))
  
;;;usm.nw:4907
(class-method with: (anObject)
    ((self new) add: anObject))
;;;usm.nw:4928
(class-method withAll: (aCollection)
    ((self new) addAll: aCollection))
;;;usm.nw:4943
(method remove: (oldObject) 
    (self remove:ifAbsent: oldObject {(self error: 'tried-to-remove-absent-object)}))
(method addAll: (aCollection) 
    (aCollection do: [block (x) (self add: x)])
    self)
(method removeAll: (aCollection) 
    (aCollection do: [block (x) (self remove: x)])
    self)
;;;usm.nw:4968
(method size () [locals temp]
    (set temp 0)
    (self do: [block (_) (set temp (temp + 1))])
    temp)
(method occurrencesOf: (anObject) [locals temp]
    (set temp 0)
    (self do: [block (x)
       ((x = anObject) ifTrue: {(set temp (temp + 1))})])
    temp)
;;;usm.nw:4985
(method isEmpty () 
    (self do: [block (_) (return false)])
    true)
(method includes: (anObject)
    (self do: [block (x) ((x = anObject) ifTrue: {(return true)})])
    false)
(method detect:ifNone: (aBlock exnBlock)
    (self do: [block (x) ((aBlock value: x) ifTrue: {(return x)})])
    (exnBlock value))
(method detect: (aBlock)
    (self detect:ifNone: aBlock {(self error: 'no-object-detected)}))
;;;usm.nw:5037
(method inject:into: (thisValue binaryBlock)
   (self do: [block (x) (set thisValue (binaryBlock value:value: x thisValue))])
   thisValue)
;;;usm.nw:5049
(method select: (aBlock) [locals temp]
   (set temp ((self species) new))
   (self do: [block (x) ((aBlock value: x) ifTrue: {(temp add: x)})])
   temp)
(method reject: (aBlock)
   (self select: [block (x) ((aBlock value: x) not)]))
(method collect: (aBlock) [locals temp]
   (set temp ((self species) new))
   (self do: [block (x) (temp add: (aBlock value: x))])
   temp)
;;;usm.nw:5063
(method species () (self class))
;;;usm.nw:5069
(method print ()
    (self printName)
    (left-round print)
    (self do: [block (x) (space print) (x print)])
    (space print)
    (right-round print)
    self)
(method printName () (((self class) name) print))
;;;usm.nw:4870
)
;;;usm.nw:5166
(class KeyedCollection
    [subclass-of Collection]  ; abstract class
    (method at:put: (key value)                (self subclassResponsibility))
    (method associationsDo: (aBlock)           (self subclassResponsibility))
    (method removeKey:ifAbsent: (key exnBlock) (self subclassResponsibility))
    
;;;usm.nw:5179
(method do: (aBlock) 
    (self associationsDo: [block (anAssoc) (aBlock value: (anAssoc value))]))
;;;usm.nw:5193
(method at: (key)    
    (self at:ifAbsent: key {(self error: 'key-not-found)}))
(method at:ifAbsent: (key exnBlock) 
    ((self associationAt:ifAbsent: key {(return (exnBlock value))}) value))
(method includesKey: (key) 
    ((self associationAt:ifAbsent: key {}) notNil))
(method associationAt: (key) 
    (self associationAt:ifAbsent: key {(self error: 'key-not-found)}))
(method associationAt:ifAbsent: (key exnBlock)
    (self associationsDo: [block (x) (((x key) = key) ifTrue: {(return x)})])
    (exnBlock value))
;;;usm.nw:5223
(method keyAtValue: (value) 
    (self keyAtValue:ifAbsent: value {(self error: 'value-not-found)}))
(method keyAtValue:ifAbsent: (value exnBlock)
    (self associationsDo: [block (x) 
        (((x value) = value) ifTrue: {(return (x key))})])
    (exnBlock value))
;;;usm.nw:5244
(method removeKey: (key)    
    (self removeKey:ifAbsent: key {(self error: 'key-not-found)}))
;;;usm.nw:5258
(method = (collection)
    (self associationsDo:
        [block (assn)
             (((assn value) = 
                          (collection at:ifAbsent: (assn key) {(return false)})) ifFalse:
                       {(return false)})])
    ((self size) = (collection size)))
;;;usm.nw:5172
)
;;;usm.nw:5332
(class SequenceableCollection
    [subclass-of KeyedCollection] ; abstract class
    (method firstKey () (self subclassResponsibility))
    (method lastKey  () (self subclassResponsibility))
    (method last     () (self at: (self  lastKey)))
    (method first    () (self at: (self firstKey)))
    (method at:ifAbsent: (index exnBlock) [locals current]
        (set current (self firstKey))
        (self do: [block (v)
            ((current = index) ifTrue: {(return v)})
            (set current (current + 1))])
        (exnBlock value))
    (method associationsDo: (bodyBlock) [locals i last]
        (set i    (self firstKey))
        (set last (self lastKey))
        ({(i <= last)} whileTrue:
            {(bodyBlock value: (Association withKey:value: i (self at: i)))
             (set i (i + 1))}))
)
;;;usm.nw:5570
(class Cons
    [subclass-of Object]
    [ivars car cdr]
    (method car ()           car)
    (method cdr ()           cdr)
    (method car: (anObject)  (set car anObject) self)
    (method cdr: (anObject)  (set cdr anObject) self)
    (method pred: (aCons)    nil)
    
;;;usm.nw:5586
(method deleteAfter () [locals answer]
    (set answer (cdr car))
    (set cdr    (cdr cdr))
    (cdr pred: self)
    answer)
(method insertAfter: (anObject)
    (set cdr (((Cons new) cdr: cdr) car: anObject))
    ((cdr cdr) pred: cdr)
    anObject)
;;;usm.nw:5612
(method do: (aBlock)
    (aBlock value: car)
    (cdr do: aBlock))
;;;usm.nw:5626
(method rejectOne:ifAbsent:withPred: (aBlock exnBlock pred)
    ((aBlock value: self) ifTrue:ifFalse:
        {(pred deleteAfter)}
        {(cdr rejectOne:ifAbsent:withPred: aBlock exnBlock self)}))
;;;usm.nw:5579
)
;;;usm.nw:5639
(class ListSentinel
    [subclass-of Cons]
    [ivars pred]
    (method pred: (aCons)   (set pred aCons))
    (method pred  ()        pred)
    (class-method new ()    
        [locals tmp]
        (set tmp (super new))
        (tmp pred: tmp)
        (tmp  cdr: tmp)
        tmp)
    
;;;usm.nw:5616
(method do: (aBlock) nil)
;;;usm.nw:5631
(method rejectOne:ifAbsent:withPred: (aBlock exnBlock pred)
    (exnBlock value))
;;;usm.nw:5650
                                                   )
;;;usm.nw:5490
(class List
    [subclass-of SequenceableCollection]
    [ivars sentinel]
    (class-method new ()        ((super new) sentinel: (ListSentinel new)))
    (method sentinel: (s)       (set sentinel s) self) ; private
    (method isEmpty   ()        (sentinel == (sentinel cdr)))
    (method last      ()        ((sentinel pred) car))
    (method do:       (aBlock)  ((sentinel cdr) do: aBlock))
    
;;;usm.nw:5508
(method addLast:  (item)   ((sentinel pred) insertAfter: item) self)
(method addFirst: (item)   (sentinel insertAfter: item)        self)
(method add:      (item)   (self addLast: item))
;;;usm.nw:5517
(method removeFirst ()     (sentinel deleteAfter))
(method removeLast  ()     (self leftAsExercise))
;;;usm.nw:5530
(method remove:ifAbsent: (oldObject exnBlock)
    ((sentinel cdr)
        rejectOne:ifAbsent:withPred:
        [block (x) (oldObject = (x car))]
        exnBlock
        sentinel))
;;;usm.nw:5540
(method removeKey:ifAbsent: (n exnBlock) (self leftAsExercise))
;;;usm.nw:5546
(method firstKey () 0)
(method lastKey  () ((self size) - 1))
(method at:put: (n value) [locals tmp]
    (set tmp (sentinel cdr))
    ({(n = 0)} whileFalse:
       {(set n (n - 1))
        (set tmp (tmp cdr))})
    (tmp car: value)
    self)
;;;usm.nw:5499
)
;;;usma.nw:2129
(class Association
   [subclass-of Object]
   [ivars key value]
   (class-method withKey:value: (x y) ((self new) setKey:value: x y))
   (method setKey:value: (x y) (set key x) (set value y) self) ; private
   (method key       ()  key)
   (method value     ()  value)
   (method setKey:   (x) (set key   x))
   (method setValue: (y) (set value y))
   (method =         (a) ((key = (a key)) & (value = (a value))))
)
;;;usma.nw:2193
(class Dictionary
    [subclass-of KeyedCollection]
    [ivars table] ; list of Associations
    (class-method new ()      ((super new) initDictionary))
    (method initDictionary () (set table (List new)) self) ; private
    
;;;usma.nw:2212
(method associationsDo: (aBlock) (table do: aBlock))
(method at:put: (key value) [locals tempassoc]
    (set tempassoc (self associationAt:ifAbsent: key {}))
    ((tempassoc isNil) ifTrue:ifFalse:
         {(table add: (Association withKey:value: key value))}
         {(tempassoc setValue: value)})
    self)
;;;usma.nw:2224
(method removeKey:ifAbsent: (key exnBlock)
   [locals value-removed] ; value found if not absent
   (set value-removed (self at:ifAbsent: key {(return (exnBlock value))}))
   (set table (table reject: [block (assn) (key = (assn key))])) ; remove assoc
   value-removed)
;;;usma.nw:2233
(method remove:ifAbsent: (value exnBlock)
   (self error: 'Dictionary-uses-remove:key:-not-remove:))
;;;usma.nw:2240
(method add: (anAssociation)
  (self at:put: (anAssociation key) (anAssociation value)))
;;;usma.nw:2245
(method print () [locals print-comma]
    (set print-comma false)
    (self printName)
    (left-round print)
    (self associationsDo:
        [block (x) (space print)
                   (print-comma ifTrue: {(', print) (space print)})
                   (set print-comma true)
                   ((x key) print)   (space print)
                   ('|--> print)     (space print)
                   ((x value) print)])
    (space print)
    (right-round print)
    self)
;;;usma.nw:2199
)
;;;usma.nw:2281
(class Array
    [subclass-of SequenceableCollection] ; representation is primitive
    (class-method new: (size) (primitive arrayNew self size))
    (class-method new  ()     (self error: 'size-of-Array-must-be-specified))
    (method size       ()     (primitive arraySize self))
    (method at:        (key)       (primitive arrayAt self key))
    (method at:put:    (key value) (primitive arrayUpdate self key value) self)
    (method printName  () nil) ; names of arrays aren't printed
    
;;;usm.nw:5728
(method add:                (x)   (self fixedSizeError))
(method remove:ifAbsent:    (x b) (self fixedSizeError))
(method removeKey:ifAbsent: (x b) (self fixedSizeError))
(method fixedSizeError      ()    (self error: 'arrays-have-fixed-size))
;;;usm.nw:5736
(method firstKey () 0)
(method lastKey  () ((self size) - 1))
(method do: (aBlock) [locals index]
    (set index (self firstKey))
    ((self size) timesRepeat:
       {(aBlock value: (self at: index))
        (set index (index + 1))}))
;;;usma.nw:2290
)
;;;usma.nw:3207
(class Set
    [subclass-of Collection]
    [ivars members]  ; list of elements [invariant: no repeats]
    (class-method new () ((super new) initSet))
    (method initSet   () (set members (List new)) self) ; private
    (method do: (aBlock) (members do: aBlock))
    (method add: (item)
        ((members includes: item) ifFalse: {(members add: item)})
        self)
    (method remove:ifAbsent: (item exnBlock) 
        (members remove:ifAbsent: item exnBlock)
        self)
    (method =  (s) [locals looks-similar]
       (set looks-similar ((self size) = (s size)))
       (looks-similar ifTrue:
           {(self do: [block (x) ((s includes: x) ifFalse:
                                           {(set looks-similar false)})])})
       looks-similar)
)
