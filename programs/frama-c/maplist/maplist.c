#include <stdlib.h>
#include "maplist.h"

maplist_t* new_list(){
    maplist_t* l = (maplist_t*) malloc(sizeof(maplist_t));
    l->head = 0;
    return l;
}

/*@ 
requires \valid(l) && unique_sorted_increasing(l->head);
assigns \nothing;
ensures \result != 0 ==> (\result->next == 0 || \result->next->key >= x);
ensures \result == 0 ==> (l->head == \null);
*/
node_t* gotoNodegteqX(maplist_t* l, int x){
    node_t* n = l->head;
    if(!n) {
        //@ assert n == 0;
        return NULL;
    }
    //@ assert n != \null;
    /*@
    loop assigns n;
    loop invariant n != \null;
    */
    while(n->next && n->next->key < x){
        //@ assert n->next != \null;
        //@ assert n->next->key < x;
        n = n->next;
        //@ assert n != \null && (n->next == \null || n->next != \null);
    }
    //@ assert n->next == \null || n->next->key >= x;
    return n;
}

int insert(maplist_t* l, int k, int v){
    node_t* n = gotoNodegteqX(l, k);
    //@ assert n == 0 || n->next == 0 || n->next->key >= k;
    if(!n) {
        l->head = (node_t*) malloc(sizeof(node_t));
        l->head->key = k;
        l->head->value = v;
        l->head->next = NULL;
        //@ assert \valid(l->head) && l->head->next == \null;
        return 1;
    }
    //@ assert n->next == 0 || n->next->key >= k;
    node_t* tmp = n->next;
    if(tmp && tmp->value == k)
        return 0;
    
    //@ assert n->next == 0 || n->next->key > k;
    n->next = (node_t*) malloc(sizeof(node_t));
    n->next->key = k;
    n->next->value = v;
    n->next->next = tmp;
    //@ assert n->next->key == k && (n->next->next == 0 || n->next->next->key > k);
    return 1;
}

int find(maplist_t* l, int k){
    node_t* n = gotoNodegteqX(l, k);
    //@ assert n == 0 || n->next == 0 || n->next->key >= k;
    if(!n) {
        //@ assert l->head == \null;
        return 0;
    }
    //@ assert n->next == 0 || n->next->key >= k;
    if(n->next && n->next->key == k)
        return n->next->value;
    
    //@ assert n->next == 0 || n->next->key > k;
    return 0;
}

int remove(maplist_t* l, int k) {
    node_t* n = gotoNodegteqX(l, k);
    //@ assert n == 0 || n->next == 0 || n->next->key >= k;
    if(!n) {
        //@ assert l->head == \null;
        return 0;
    }
    //@ assert n->next == 0 || n->next->key >= k;
    node_t* tmp = n->next;
    if(tmp && tmp->value == k){
        //@ assert n->next->key == k && n->next->next->key > k;
        n->next = tmp->next;                    
        //@ assert n->next->key > k;
        free((void*)tmp);
        return 1;
    }
    
    //@ assert n->next == 0 || n->next->key > k;
    return 0;
}