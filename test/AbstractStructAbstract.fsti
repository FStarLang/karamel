module AbstractStructAbstract

val t (a:Type0) : Type0

val make (#a:Type0) (x:a) : t a
val read (#a:Type0) (x:t a) : a
