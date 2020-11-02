#include <stdlib.h>
#include "linkedlist.h"

linkedlist_t* new_list(){
    linkedlist_t* l = (linkedlist_t*) malloc(sizeof(linkedlist_t));
    l->head = 0;
    return l;
}

/*@ 
requires \valid(l) && unique_sorted_increasing(l->head);
assigns \nothing;
ensures \result != 0 ==> (\result->next == 0 || \result->next->value >= x);
ensures \result == 0 ==> (l->head == \null);
*/
node_t* gotoNodegteqX(linkedlist_t* l, int x){
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
    while(n->next && n->next->value < x){
        //@ assert n->next != \null;
        //@ assert n->next->value < x;
        n = n->next;
        //@ assert n != \null && (n->next == \null || n->next != \null);
    }
    //@ assert n->next == \null || n->next->value >= x;
    return n;
}

int insert(linkedlist_t* l, int x){
    node_t* n = gotoNodegteqX(l, x);
    //@ assert n == 0 || n->next == 0 || n->next->value >= x;
    if(!n) {
        l->head = (node_t*) malloc(sizeof(node_t));
        l->head->value = x;
        l->head->next = NULL;
        //@ assert \valid(l->head) && l->head->next == \null;
        return 1;
    }
    //@ assert n->next == 0 || n->next->value >= x;
    node_t* tmp = n->next;
    if(tmp && tmp->value == x)
        return 0;
    
    //@ assert n->next == 0 || n->next->value > x;
    n->next = (node_t*) malloc(sizeof(node_t));
    n->next->value = x;
    n->next->next = tmp;
    //@ assert n->next->value == x && (n->next->next == 0 || n->next->next->value > x);
    return 1;
}

int find(linkedlist_t* l, int x){
    node_t* n = gotoNodegteqX(l, x);
    //@ assert n == 0 || n->next == 0 || n->next->value >= x;
    if(!n) {
        //@ assert l->head == \null;
        return 0;
    }
    //@ assert n->next == 0 || n->next->value >= x;
    if(n->next && n->next->value == x)
        return 1;
    
    //@ assert n->next == 0 || n->next->value > x;
    return 0;
}

int remove(linkedlist_t* l, int x) {
    node_t* n = gotoNodegteqX(l, x);
    //@ assert n == 0 || n->next == 0 || n->next->value >= x;
    if(!n) {
        //@ assert l->head == \null;
        return 0;
    }
    //@ assert n->next == 0 || n->next->value >= x;
    node_t* tmp = n->next;
    if(tmp && tmp->value == x){
        //@ assert n->next->value == x && n->next->next->value > x;
        n->next = tmp->next;                    
        //@ assert n->next->value > x;
        free((void*)tmp);
        return 1;
    }
    
    //@ assert n->next == 0 || n->next->value > x;
    return 0;
}