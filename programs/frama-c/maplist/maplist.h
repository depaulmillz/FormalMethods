#pragma once

typedef struct _node {
    int key;
    int value;
    struct _node* next;
} node_t;

typedef struct _maplist {
    node_t* head;
} maplist_t;

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
     root->key < root->next->key && 
        unique_sorted_increasing(root->next) ==> unique_sorted_increasing(root); 
}
*/ 

/*@ 
inductive does_not_use_invalid_value{L}(node_t* root) { 
  case does_not_use_invalid_value_nil{L}: does_not_use_invalid_value(\null); 
  case does_not_use_invalid_value_singleton{L}: 
  \forall node_t* root; 
     \valid(root) && root->next == \null && root->value != 0 ==> does_not_use_invalid_value(root); 
  case does_not_use_invalid_value_next{L}: 
  \forall node_t* root; 
     \valid(root) && \valid(root->next) && 
     root->value != 0 && 
        does_not_use_invalid_value(root->next) ==> does_not_use_invalid_value(root); 
}
*/ 


/*@ 
axiomatic Count { 
  logic integer count(int x,node_t* l); 
 
  axiom count_nil: \forall int x; count(x,\null) == 0; 
 
  axiom count_cons_head{L}: 
  \forall int x,node_t* l; 
    \valid(l) && l->key == x ==> 
       count(x,l) == count(x,l->next)+1; 
 
 axiom count_cons_tail{L}: 
  \forall int x, node_t* l; 
     \valid(l) && l->key != x ==> 
        count(x,l) == count(x,l->next); 
} 
*/ 


/*@ 
axiomatic Contains { 
  logic integer contains(int x,node_t* l); 
 
  axiom contains_nil: \forall int x; contains(x,\null) == 0; 
 
  axiom contains_cons_head{L}: 
  \forall int x,node_t* l; 
    \valid(l) && l->key == x ==> 
       contains(x,l) == 1; 
 
 axiom contains_cons_tail{L}: 
  \forall int x, node_t* l; 
     \valid(l) && l->key != x ==> 
        contains(x,l) == contains(x,l->next); 
} 
*/ 

/*@ 
axiomatic Get { 
  logic integer get(int x,node_t* l); 
 
  axiom get_nil: \forall int x; get(x,\null) == 0; 
 
  axiom get_cons_head{L}: 
  \forall int x,node_t* l; 
    \valid(l) && l->key == x ==> 
       get(x,l) == l->value; 
 
 axiom get_cons_tail{L}: 
  \forall int x, node_t* l; 
     \valid(l) && l->key != x ==> 
        get(x,l) == get(x,l->next); 
}
*/ 


/*@
ensures \valid(\result) && \result->head == \null && unique_sorted_increasing(\result->head);
ensures does_not_use_invalid_value(\result->head);
*/
maplist_t* new_list();

/*@ 
requires \valid(l) && unique_sorted_increasing(l->head) && v != 0;
ensures unique_sorted_increasing(l->head);
ensures does_not_use_invalid_value(l->head);
*/
int insert(maplist_t* l, int k, int v);

/*@
requires \valid(l) && unique_sorted_increasing(l->head);
assigns \nothing;
ensures \result == get(k, l->head);
ensures does_not_use_invalid_value(l->head);
*/
int get(maplist_t* l, int k);

/*@
requires \valid(l) && unique_sorted_increasing(l->head);
ensures \result == 1 ==> contains(k, l->head) == 0;
ensures unique_sorted_increasing(l->head);
ensures does_not_use_invalid_value(l->head);
*/
int remove(maplist_t* l, int k);