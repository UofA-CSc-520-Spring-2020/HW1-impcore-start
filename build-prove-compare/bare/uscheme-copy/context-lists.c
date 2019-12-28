#include "all.h"
/* context-lists.c S193e */
/* private functions for updating lists of expressions in contexts S194b */
static void fill_hole(Exp e, Value v) {
  assert(e->alt == HOLE);
  e->alt = LITERAL;
  e->u.literal = v;
}
/* private functions for updating lists of expressions in contexts S194c */
static Explist find_explist_hole(Explist es) {
  while (es && es->hd->alt != HOLE)
    es = es->tl;
  return es;
}
/* context-lists.c S194a */
Exp transition_explist(Explist es, Value v) {
  Explist p = find_explist_hole(es);
  assert(p);
  fill_hole(p->hd, v);
  return head_replaced_with_hole(p->tl);
}
/* context-lists.c S194d */
Exp head_replaced_with_hole(Explist es) {
  static struct Exp a_copy; // overwritten by subsequent calls
  if (es) {
    a_copy = *es->hd;
    *es->hd = mkHoleStruct();
    return &a_copy;
  } else {
    return NULL;
  }
}
/* context-lists.c S194e */
Explist copyEL(Explist es) {
  if (es == NULL)
    return NULL;
  else {
    Exp e = malloc(sizeof(*e));
    assert(e);
    *e = *es->hd;
    return mkEL(e, copyEL(es->tl));
  }
}
/* context-lists.c S195a */
void freeEL(Explist es) {
  if (es != NULL) {
    freeEL(es->tl);
    free(es->hd);
    free(es);
  }
}
/* context-lists.c S195b */
void freeVL(Valuelist vs) {
  if (vs != NULL) {
    freeVL(vs->tl);
    free(vs);
  }
}
/* context-lists.c S195c */
Valuelist asLiterals(Explist es) {
  if (es == NULL)
    return NULL;
  else
    return mkVL(asLiteral(es->hd), asLiterals(es->tl));

}
/* context-lists.c S195d */
Value asLiteral(Exp e) {
  assert(e->alt == LITERAL);
  return validate(e->u.literal);
}
