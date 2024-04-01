WeChat: cstutorcs
QQ: 749389476
Email: tutorcs@163.com
#define NULL ((void *)0)

struct block {
  struct blist *nexts;
  int flag;
  int data;
  struct block *m_nxt; /* marked list */
};


struct blist {
  struct block *this;
  struct blist *next;
};


struct blist *append_step(struct blist *l1, struct blist *l2)
{
  struct blist *tmp = l1->next;
  l1->next = l2;
  l2 = l1;
  l1 = tmp;
  return l1;
} 


struct blist *append(struct blist *l1, struct blist *l2)
{
  while (l1) {
    struct blist *tmp = append_step (l1, l2);
    l2 = l1;
    l1 = tmp;
  }
  return l2;
} 


struct block *mark(struct blist *roots)
{
  struct block *cur;
  cur->m_nxt = NULL;
  struct block *mkdlist = NULL;
  
  while (roots) { 
    cur = roots->this;
    roots = roots->next;
  
    if (!cur->flag) {
      cur->flag = 1;
      cur->m_nxt = mkdlist;
      mkdlist = cur;
      roots = append(cur->nexts,roots);
    }
  }

  return mkdlist;
}

