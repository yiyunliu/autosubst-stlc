tm : Type
ty : Type

lam : (tm -> tm) -> tm
app : tm -> tm -> tm
unit : tm

TUnit : ty
TPi : ty -> ty -> ty
