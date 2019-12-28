;;;usm.nw:6823
(class LargeInteger
  [subclass-of Integer]
  [ivars magnitude]

  (class-method withMagnitude: (aNatural)
      ((self new) magnitude: aNatural))
  (method magnitude: (aNatural) ; private, for initialization
      (set magnitude aNatural)
      self)

  (method magnitude () magnitude)

  (class-method fromSmall: (anInteger)
     ((anInteger isNegative) ifTrue:ifFalse: 
        {(((self new: 1) + (self new: ((anInteger + 1) negated))) negated)}
        {((LargePositiveInteger new) magnitude: (Natural new: anInteger))}))
  (method asLargeInteger () self)
  (method isZero () (magnitude isZero))
  (method = (anInteger) ((self - anInteger)     isZero))
  (method < (anInteger) ((self - anInteger) isNegative))

  (method div: (_) (self error: 'long-division-not-supported))
  (method mod: (_) (self error: 'long-division-not-supported))

  (method sdiv: (aSmallInteger) (self leftAsExercise))
  (method smod: (aSmallInteger) (self leftAsExercise))
)
