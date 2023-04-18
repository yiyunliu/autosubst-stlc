tm : Type
sort : Type

lam : (tm -> tm) -> tm
app : tm -> tm -> tm
pi : tm -> (tm -> tm) -> tm
type : sort -> tm

TYPE : sort
KIND : sort