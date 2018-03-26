#ifndef _LIST_H
#define _LIST_H

#define declare_list_type(t) struct t##_list { t* t##_elem; struct t##_list* next; }; \
  struct t##_list* make_##t##_list(t* p, struct t##_list* l);	\
  void t##_list_free(struct t##_list* l);				\
  int t##_list_size(const struct t##_list* l); \
  struct t##_list* t##_list_find(struct t##_list* l, unsigned char (*pred)(t* elem)); \
  const struct t##_list* t##_list_find_const(const struct t##_list* l, unsigned char (*pred)(const t* elem));

#define impl_list_type(t) struct t##_list* make_##t##_list(t* p, struct t##_list* l) { struct t##_list* pl = malloc(sizeof(struct t##_list)); pl->t##_elem = p; pl->next = l; return pl; } \
  void t##_list_free(struct t##_list* l) {  if (!l) return; t##_free(l->t##_elem);  t##_list_free(l->next);  free(l); } \
  int t##_list_size(const struct t##_list* l) { int s=0; while (l) {s++; l=l->next;} return s; } \
  struct t##_list* t##_list_find(struct t##_list* l, unsigned char (*pred)(t* elem)) { while(l) { if (pred(l->t##_elem)) return l; l=l->next;} return 0; } \
  const struct t##_list* t##_list_find_const(const struct t##_list* l, unsigned char (*pred)(const t* elem)) { while(l) { if (pred(l->t##_elem)) return l; l=l->next;} return 0; }

struct string_list
{
  char* string_elem;
  struct string_list* next;
};
struct string_list* make_string_list(char* elem, struct string_list* next);
void string_list_free(struct string_list* l);
int string_list_size(const struct string_list* l);
short string_list_contains(const struct string_list* l, const char* string);

#define declare_set_type(t) typedef void* t##_set; \
	t* t##_set_find(const t* x, t##_set s);

#define impl_set_type(t, comp) t* t##_set_find(const t* x, t##_set s) { t** y = tfind(x, (void**)&s, comp); return y ? *y : 0; }

#endif
