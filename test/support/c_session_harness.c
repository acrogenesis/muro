#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static char g_name[256];

static char *copy_str(const char *s) {
  size_t n = strlen(s) + 1;
  char *p = malloc(n);
  if (!p) abort();
  memcpy(p, s, n);
  return p;
}

static void put_field(const char *s) {
  size_t n = s ? strlen(s) : 0;
  printf("%zu\n", n);
  if (n) fwrite(s, 1, n, stdout);
  fputc('\n', stdout);
}

static void show(const muro__sess_res *res) {
  const char *at = muro__sess_at(g_name, res->state);
  printf("status %d\n", res->status);
  printf("done %d\n", res->done);
  put_field(res->step);
  put_field(res->expected);
  put_field(at ? at : "");
  printf(".\n");
  fflush(stdout);
}

static const char *skip(const char *s) {
  while (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r') s++;
  return s;
}

static int take_word(const char **ps, char *buf, size_t n) {
  const char *s = skip(*ps);
  size_t i = 0;
  if (*s == 0) return 0;
  while (*s && *s != ' ' && *s != '\t' && *s != '\n' && *s != '\r' && i + 1 < n) {
    buf[i++] = *s++;
  }
  buf[i] = 0;
  *ps = s;
  return 1;
}

static int take_u64(const char **ps, uint64_t *out) {
  char buf[80];
  char *end = 0;
  unsigned long long x;
  if (!take_word(ps, buf, sizeof buf)) return 0;
  x = strtoull(buf, &end, 10);
  if (!end || *end) return 0;
  *out = (uint64_t)x;
  return 1;
}

static muro__sess_val *parse_val(const char **ps);

static muro__sess_val *box(uint8_t tag) {
  muro__sess_val *v = calloc(1, sizeof *v);
  if (!v) abort();
  v->tag = tag;
  return v;
}

static int parse_many(const char **ps, uint64_t n, muro__sess_val **out) {
  muro__sess_val *items;
  uint64_t i;
  if (n > 64) return 0;
  items = calloc((size_t)(n ? n : 1), sizeof *items);
  if (!items) abort();
  for (i = 0; i < n; i++) {
    muro__sess_val *one = parse_val(ps);
    if (!one) {
      free(items);
      return 0;
    }
    items[i] = *one;
    free(one);
  }
  *out = items;
  return 1;
}

static muro__sess_val *parse_val(const char **ps) {
  char w[256];
  muro__sess_val *v;
  if (!take_word(ps, w, sizeof w)) return 0;
  if (!strcmp(w, "nat")) {
    v = box(MURO_SESS_NAT);
    if (!take_u64(ps, &v->nat)) return 0;
    return v;
  }
  if (!strcmp(w, "bit")) {
    uint64_t b;
    v = box(MURO_SESS_BIT);
    if (!take_u64(ps, &b) || b > 1) return 0;
    v->bit = (uint8_t)b;
    return v;
  }
  if (!strcmp(w, "unit")) return box(MURO_SESS_UNIT);
  if (!strcmp(w, "pick")) {
    uint64_t b;
    v = box(MURO_SESS_PICK);
    if (!take_u64(ps, &b) || b > 1) return 0;
    v->bit = (uint8_t)b;
    return v;
  }
  if (!strcmp(w, "pair")) {
    muro__sess_val *a = parse_val(ps);
    muro__sess_val *b = parse_val(ps);
    if (!a || !b) return 0;
    v = box(MURO_SESS_PAIR);
    v->a = a;
    v->b = b;
    return v;
  }
  if (!strcmp(w, "vec")) {
    uint64_t n;
    muro__sess_val *items = 0;
    if (!take_u64(ps, &n) || !parse_many(ps, n, &items)) return 0;
    v = box(MURO_SESS_VEC);
    v->n = n;
    v->a = items;
    return v;
  }
  if (!strcmp(w, "rec")) {
    uint64_t n, i;
    muro__sess_val *items;
    const char **names;
    if (!take_u64(ps, &n) || n > 64) return 0;
    items = calloc((size_t)(n ? n : 1), sizeof *items);
    names = calloc((size_t)(n ? n : 1), sizeof *names);
    if (!items || !names) abort();
    for (i = 0; i < n; i++) {
      char name[256];
      muro__sess_val *one;
      if (!take_word(ps, name, sizeof name)) return 0;
      one = parse_val(ps);
      if (!one) return 0;
      names[i] = copy_str(name);
      items[i] = *one;
      free(one);
    }
    v = box(MURO_SESS_REC);
    v->n = n;
    v->a = items;
    v->names = names;
    return v;
  }
  if (!strcmp(w, "data")) {
    char ctor[256];
    uint64_t n;
    muro__sess_val *items = 0;
    if (!take_word(ps, ctor, sizeof ctor) || !take_u64(ps, &n)) return 0;
    if (!parse_many(ps, n, &items)) return 0;
    v = box(MURO_SESS_DATA);
    v->ctor = copy_str(ctor);
    v->n = n;
    v->a = items;
    return v;
  }
  return 0;
}

static int cmd_init(const char *s, muro__sess_st *st) {
  char name[256];
  uint64_t n, i;
  uint64_t *args;
  muro__sess_res res;
  if (!take_word(&s, name, sizeof name) || !take_u64(&s, &n) || n > 16) return 0;
  args = calloc((size_t)(n ? n : 1), sizeof *args);
  if (!args) abort();
  for (i = 0; i < n; i++) {
    if (!take_u64(&s, &args[i])) return 0;
  }
  snprintf(g_name, sizeof g_name, "%s", name);
  res = muro__sess_init(g_name, args, (size_t)n);
  *st = res.state;
  show(&res);
  free(args);
  return 1;
}

static int cmd_step(const char *s, muro__sess_st *st) {
  char dirw[32];
  int dir;
  muro__sess_val *v = 0;
  muro__sess_res res;
  if (!take_word(&s, dirw, sizeof dirw)) return 0;
  if (!strcmp(dirw, "send")) dir = MURO_SESS_SEND;
  else if (!strcmp(dirw, "recv")) dir = MURO_SESS_RECV;
  else if (!strcmp(dirw, "bad")) dir = 0;
  else return 0;
  if (strcmp(dirw, "bad") != 0) {
    v = parse_val(&s);
    if (!v) return 0;
  }
  res = muro__sess_step(g_name, *st, dir, v);
  if (res.status == MURO_SESS_OK) *st = res.state;
  show(&res);
  return 1;
}

int main(void) {
  char line[65536];
  muro__sess_st st;
  memset(&st, 0, sizeof st);
  while (fgets(line, sizeof line, stdin)) {
    const char *s = skip(line);
    if (*s == 0 || *s == '#') continue;
    if (!strncmp(s, "init ", 5)) {
      if (!cmd_init(s + 5, &st)) return 2;
    } else if (!strncmp(s, "step ", 5)) {
      if (!cmd_step(s + 5, &st)) return 2;
    } else {
      return 2;
    }
  }
  return 0;
}
