#pragma once

typedef struct _node {
    int value;
    struct _node* next;
} node_t;

typedef struct _linkedlist {
    node_t* head;
} linkedlist_t;

/*@
inductive reachable{L} (node_t* root, node_t* node) {
    case root_reachable{L}:
        \forall node_t* root; reachable(root,root);
    case next_reachable{L}:
        \forall node_t* root, *node;
        \valid(root) ==> reachable(root->next, node) ==> reachable(root,node);
} 
*/

/*@ 
inductive unique_sorted_increasing{L}(node_t* root) { 
  case sorted_nil{L}: unique_sorted_increasing(\null); 
  case sorted_singleton{L}: 
  \forall node_t* root; 
     \valid(root) && root->next == \null ==> unique_sorted_increasing(root); 
  case sorted_next{L}: 
  \forall node_t* root; 
     \valid(root) && \valid(root->next) && 
     root->value < root->next->value && 
        unique_sorted_increasing(root->next) ==> unique_sorted_increasing(root); 
}
*/ 

/*@ 
axiomatic Count { 
  logic integer count(int x,node_t* l); 
 
  axiom count_nil: \forall int x; count(x,\null) == 0; 
 
  axiom count_cons_head{L}: 
  \forall int x,node_t* l; 
    \valid(l) && l->value == x ==> 
       count(x,l) == count(x,l->next)+1; 
 
 axiom count_cons_tail{L}: 
  \forall int x, node_t* l; 
     \valid(l) && l->value != x ==> 
        count(x,l) == count(x,l->next); 
} 
*/ 


/*@ 
axiomatic Contains { 
  logic integer contains(int x,node_t* l); 
 
  axiom contains_nil: \forall int x; contains(x,\null) == 0; 
 
  axiom contains_cons_head{L}: 
  \forall int x,node_t* l; 
    \valid(l) && l->value == x ==> 
       contains(x,l) == 1; 
 
 axiom contains_cons_tail{L}: 
  \forall int x, node_t* l; 
     \valid(l) && l->value != x ==> 
        contains(x,l) == contains(x,l->next); 
} 
*/ 

/*@
ensures \valid(\result) && \result->head == \null && unique_sorted_increasing(\result->head);
*/
linkedlist_t* new_list();

/*@ 
requires \valid(l) && unique_sorted_increasing(l->head);
ensures unique_sorted_increasing(l->head);
*/
int insert(linkedlist_t* l, int x);

/*@
requires \valid(l) && unique_sorted_increasing(l->head);
assigns \nothing;
ensures \result == contains(x, l->head);
*/
int find(linkedlist_t* l, int x);

/*@
requires \valid(l) && unique_sorted_increasing(l->head);
ensures \result == 1 ==> contains(x, l->head) == 0;
ensures unique_sorted_increasing(l->head);
*/
int remove(linkedlist_t* l, int x);