//This file parse the input query into a parse tree.
#include <iostream>
#include <string>
using namespace std;

class Node 
{
public:
    Node(): childnum(0),tuplenum(0),indisk(true),memfront(false),relationlocation(NULL)
    {
        for(int i=0;i<20;i++)   children[i]=NULL;
    }
    
    bool indisk;
    Relation* relationlocation;
    bool memfront;
    int tuplenum;
    vector<string> involvedtable;
    vector<string> fieldname;
    vector<int> valuecount;
    string value;
    int childnum;
    Node* children[20];
};

class Scanner 
{
    int scancount;

public:
    Scanner(): scancount(0) {}
    
    int showposition()
    {
        return scancount;
    }
    
    string scan(string query)
    {
        while(query[scancount]==' ')    scancount++;
        char c=query[scancount++];
        if(!isdigit(c) && !isalpha(c))    return string(1,c);
        else
        {
            string res=string(1,c);
            if(isdigit(c)) return integer(query,res);
            else return word(query,res);
        }
    }
    
    string integer(string query,string& res)
    {
        while(isdigit(query[scancount]))
        {
            res+=query[scancount++];
        }
        return res;
    }
    
    string word(string query,string& res)
    {
        while(isalpha(query[scancount]) || isdigit(query[scancount]))
        {
            res+=query[scancount++];
        }
        return res;
    }
    
};

class Parser
{
    bool error;
    
public:
    Parser(): error(false) {}
    
    bool showerror()
    {
        return error;
    }
    
    Node* parse(string query)
    {
        Scanner sc;
        string stat=sc.scan(query);
        Node* a=new Node();
        if(stat=="CREATE")    return create_table_statement(sc,query);
        if(stat=="DROP")  return drop_table_statement(sc,query);
        if(stat=="SELECT")    return select_statement(sc,query);
        if(stat=="DELETE")    return delete_statement(sc,query);
        if(stat=="INSERT")    return insert_statement(sc,query);
        error=true;
        return a;
    }
    
    Node* create_table_statement(Scanner& sc,string query)
    {
        string stat;
        int i=0;
        Node* a=new Node();
        a->value="create_table_statement";
        Node* b=new Node();
        b->value="CREATE";
        b->childnum=0;
        a->children[i++]=b;
        stat=sc.scan(query);
        if(stat=="TABLE")
        {
            Node* c=new Node();
            c->value="TABLE";
            c->childnum=0;
            a->children[i++]=c;
        }
        stat=sc.scan(query);
        Node* d=new Node();
        d->value="table_name";
        d->childnum=1;
        Node* e=new Node();
        e->value=stat;
        e->childnum=0;
        a->children[i++]=d;
        d->children[0]=e;
        stat=sc.scan(query);
        if(stat=="(")
        {
            stat=sc.scan(query);
            a->children[i++]=attribute_type_list(sc,query,stat);
        }
        a->childnum=i;
        return a;
    }
    
    Node* attribute_type_list(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="attribute_type_list";
        Node* b=new Node();
        b->value="attribute_name";
        b->childnum=1;
        Node* c=new Node();
        c->value=stat;
        c->childnum=0;
        a->children[i++]=b;
        b->children[0]=c;
        stat=sc.scan(query);
        Node* d=new Node();
        d->value="data_type";
        d->childnum=1;
        Node* e=new Node();
        e->value=stat;
        e->childnum=0;
        a->children[i++]=d;
        d->children[0]=e;       
        stat=sc.scan(query);
        if(stat==",")
        {
            Node* f=new Node();
            f->value=",";
            f->childnum=0;
            a->children[i++]=f;
            stat=sc.scan(query);
            a->children[i++]=attribute_type_list(sc,query,stat);
        }
        a->childnum=i;
        return a;         
    }
    
    Node* drop_table_statement(Scanner& sc,string query)
    {
        int i=0;
        string stat;
        Node* a=new Node();
        a->value="drop_table_statement";
        Node* b=new Node();
        b->value="DROP";
        b->childnum=0;
        a->children[i++]=b;
        stat=sc.scan(query);
        if(stat=="TABLE")
        {
            Node* c=new Node();
            c->value=stat;
            c->childnum=0;
            a->children[i++]=c;
        }
        stat=sc.scan(query);
        Node* d=new Node();
        d->value="table_name";
        d->childnum=1;
        Node* e=new Node();
        e->value=stat;
        e->childnum=0;
        a->children[i++]=d;
        d->children[0]=e;
        a->childnum=i;
        return a;
    }
    
    Node* select_statement(Scanner& sc,string query)
    {
        int i=0;
        Node* a=new Node();
        a->value="select_statement";
        Node* b=new Node();
        b->value="SELECT";
        b->childnum=0;
        a->children[i++]=b;
        string stat=sc.scan(query);
        if(stat=="DISTINCT")
        {
            Node* c=new Node();
            c->value="DISTINCT";
            c->childnum=0;
            a->children[i++]=c;
            stat=sc.scan(query);
        }
        a->children[i++]=select_list(sc,query,stat);
        if(stat=="FROM")
        {
            Node* d=new Node();
            d->value="FROM";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
        }
        else    error=true;
        a->children[i++]=table_list(sc,query,stat);
        if(stat=="WHERE")
        {
            Node* k=new Node();
            k->value="WHERE";
            k->childnum=0;
            a->children[i++]=k;
            stat=sc.scan(query);
            a->children[i++]=search_condition(sc,query,stat);            
        }
        if(stat=="ORDER")
        {
            Node* e=new Node();
            e->value="ORDER";
            e->childnum=0;
            a->children[i++]=e;
            stat=sc.scan(query);
            if(stat=="BY")
            {
                Node* f=new Node();
                f->value="BY";
                f->childnum=0;
                a->children[i++]=f;
            }
            else    error=true;
            stat=sc.scan(query);
            Node* h=new Node();
            h->value="column_name";
            Node* pa=new Node();
            pa->value="attribute_name";
            pa->childnum=1;
            Node* g=new Node();
            g->value=stat;
            g->childnum=0;
            stat=sc.scan(query);
            if(stat==".")
            {
                Node* pc=new Node();
                pc->value="table_name";
                pc->childnum=1;
                pc->children[0]=g;
                stat=sc.scan(query);
                Node* pb=new Node();
                pb->value=stat;
                pb->childnum=0;
                pa->children[0]=pb;
                h->children[0]=pc;
                Node* pd=new Node();
                pd->value=".";
                pd->childnum=0;
                h->children[1]=pd;
                h->children[2]=pa;
                h->childnum=3;
            }
            else
            {
                pa->children[0]=g;
                h->children[0]=pa;
                h->childnum=1;
            }
            a->children[i++]=h;
        }
        a->childnum=i;
        return a;
    }
    
    Node* delete_statement(Scanner& sc,string query)
    {
        int i=0;
        string stat;
        Node* a=new Node();
        a->value="delete_statement";
        Node* b=new Node();
        b->value="DELETE";
        b->childnum=0;
        a->children[i++]=b;
        stat=sc.scan(query);
        if(stat=="FROM")
        {
            Node* c=new Node();
            c->value=stat;
            c->childnum=0;
            a->children[i++]=c;
        }
        stat=sc.scan(query);
        Node* e=new Node();
        e->value="table_name";
        e->childnum=1;
        Node* f=new Node();
        f->value=stat;
        f->childnum=0;
        a->children[i++]=e;
        e->children[0]=f;
        stat=sc.scan(query);
        if(stat=="WHERE")
        {
            Node* d=new Node();
            d->value="WHERE";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
            a->children[i++]=search_condition(sc,query,stat);
        }
        a->childnum=i;
        return a;
    }
    
    Node* insert_statement(Scanner& sc,string query)
    {
        int i=0;
        string stat;
        Node* a=new Node();
        a->value="insert_statement";
        Node* b=new Node();
        b->value="INSERT";
        b->childnum=0;
        a->children[i++]=b;
        stat=sc.scan(query);
        if(stat=="INTO")
        {
            Node* c=new Node();
            c->value=stat;
            c->childnum=0;
            a->children[i++]=c;
        }
        stat=sc.scan(query);
        Node* e=new Node();
        e->value="table_name";
        e->childnum=1;
        Node* f=new Node();
        f->value=stat;
        f->childnum=0;
        a->children[i++]=e;
        e->children[0]=f;
        stat=sc.scan(query);
        if(stat=="(")
        {
            stat=sc.scan(query);
            a->children[i++]=attribute_list(sc,query,stat);
        }
        stat=sc.scan(query);
        a->children[i++]=insert_tuples(sc,query,stat);
        a->childnum=i;
        return a;
    }
    
    Node* attribute_list(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="attribute_list";
        Node* b=new Node();
        b->value="attribute_name";
        Node* c=new Node();
        c->value=stat;
        c->childnum=0;
        b->children[0]=c;
        b->childnum=1;
        a->children[i++]=b;
        stat=sc.scan(query);
        if(stat==",")
        {
            Node* d=new Node();
            d->value=",";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
            a->children[i++]=attribute_list(sc,query,stat);
        }
        a->childnum=i;
        return a;
    }
    
    Node* insert_tuples(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="insert_tuples";
        if(stat=="SELECT")
        {
            a->children[i++]=select_statement(sc,query);
        }
        else
        {
            if(stat=="VALUES")
            {
                Node* b=new Node();
                b->value="VALUES";
                b->childnum=0;
                a->children[i++]=b;
                stat=sc.scan(query);
                if(stat=="(")
                {
                    stat=sc.scan(query);
                    a->children[i++]=value_list(sc,query,stat);
                }
            }
        }
        a->childnum=i;
        return a;
    }
    
    Node* value_list(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="value_list";
        Node* b=new Node();
        b->value="value";
        Node* c=new Node();
        if(stat=="NULL")
        {
            c->value=stat;
            c->childnum=0;
            b->children[0]=c;
            b->childnum=1;
            a->children[i++]=b;
        }
        else
        {
            if(isdigit(stat[0]))
            {
                c->value="integer";
                c->childnum=1;
                Node* d=new Node();
                d->value=stat;
                d->childnum=0;
                c->children[0]=d;
                b->children[0]=c;
                b->childnum=1;
                a->children[i++]=b;                
            }
            else
            {
                if(stat=="\"")
                {
                    stat=sc.scan(query);
                    c->value="literal";
                    c->childnum=1;
                    Node* d=new Node();
                    d->value=stat;
                    d->childnum=0;
                    c->children[0]=d;
                    b->children[0]=c;
                    b->childnum=1;
                    a->children[i++]=b;
                    stat=sc.scan(query);
                }
            }
        }
        stat=sc.scan(query);
        if(stat==",")
        {
            Node* d=new Node();
            d->value=",";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
            a->children[i++]=value_list(sc,query,stat);
        }
        a->childnum=i;
        return a;
    }
    
    
    Node* select_list(Scanner& sc,string query,string& stat)
    {
        Node* a=new Node();
        a->value="select_list";
        Node* b=new Node();
        if(stat=="*")
        {
            stat=sc.scan(query);
            b->value="*";
            b->childnum=0;
            a->children[0]=b;
            a->childnum=1;
            return a;
        }
        else
        {
            a->children[0]=select_sublist(sc,query,stat);
            a->childnum=1;
            return a;
        }
    }
    
    Node* table_list(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="table_list";
        Node* b=new Node();
        b->value="table_name";
        Node* c=new Node();
        c->value=stat;
        c->childnum=0;
        b->children[0]=c;
        b->childnum=1;
        a->children[i++]=b;
        stat=sc.scan(query);
        if(stat==",")
        {
            Node* d=new Node();
            d->value=",";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
            a->children[i++]=table_list(sc,query,stat);
        }
        a->childnum=i;
        return a;
    }
    
    Node* search_condition(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="search_condition";
        a->children[i++]=boolean_term(sc,query,stat);
        if(stat=="OR")
        {
            Node* d=new Node();
            d->value="OR";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
            a->children[i++]=search_condition(sc,query,stat);
        }
        a->childnum=i;
        return a;
    }
    
    Node* select_sublist(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="select_sublist";
        if(query[sc.showposition()]!='.')
        {
            Node* b=new Node();
            b->value="column_name";
            Node* e=new Node();
            e->value="attribute_name";
            e->childnum=1;
            Node* c=new Node();
            c->value=stat;
            c->childnum=0;
            b->children[0]=e;
            e->children[0]=c;
            b->childnum=1;
            a->children[i++]=b;
        }
        else
        {
            Node* b=new Node();
            b->value="column_name";
            Node* f=new Node();
            f->value="table_name";
            f->childnum=1;
            Node* g=new Node();
            g->value=stat;
            g->childnum=0;
            b->children[0]=f;
            f->children[0]=g;
            stat=sc.scan(query);
            stat=sc.scan(query);
            Node* e=new Node();
            e->value="attribute_name";
            e->childnum=1;
            Node* c=new Node();
            c->value=stat;
            c->childnum=0;
            b->children[1]=e;
            e->children[0]=c;
            b->childnum=2;
            a->children[i++]=b;
        }
        stat=sc.scan(query);
        if(stat==",")
        {
            Node* d=new Node();
            d->value=",";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
            a->children[i++]=select_sublist(sc,query,stat);
        }
        a->childnum=i;
        return a;
    }
    
    Node* boolean_term(Scanner& sc,string query,string& stat)
    {
        int i=0;
        Node* a=new Node();
        a->value="boolean_term";
        a->children[i++]=boolean_factor(sc,query,stat);
        stat=sc.scan(query);
        if(stat=="AND")
        {
            Node* d=new Node();
            d->value="AND";
            d->childnum=0;
            a->children[i++]=d;
            stat=sc.scan(query);
            a->children[i++]=boolean_term(sc,query,stat);
        }
        a->childnum=i;
        return a;        
    }
    
    Node* boolean_factor(Scanner& sc,string query,string& stat)
    {
        Node* a=new Node();
        a->value="boolean_factor";
        a->children[0]=expression(sc,query,stat);
        stat=sc.scan(query);
        Node* b=new Node();
        b->value="comp_op";
        Node* c=new Node();
        c->value=stat;
        c->childnum=0;
        b->children[0]=c;
        a->children[1]=b;
        b->childnum=1;
        stat=sc.scan(query);
        a->children[2]=expression(sc,query,stat);
        a->childnum=3;
        return a;
    }
    
    Node* expression(Scanner& sc,string query,string& stat)
    {
        Node* a=new Node();
        a->value="expression";        
        if(stat!="(")
        {
            Node* b=new Node();
            b->value="term";
            a->children[0]=b;
            b->childnum=1;
            b->children[0]=term(sc,query,stat);
            a->childnum=1;
        }
        else
        {
            stat=sc.scan(query);
            Node* c=new Node();
            c->value="term";
            c->children[0]=term(sc,query,stat);
            a->children[0]=c;
            stat=sc.scan(query);
            Node* d=new Node();
            d->value=stat;
            d->childnum=0;
            c->childnum=1;
            a->children[1]=d;
            stat=sc.scan(query);
            Node* f=new Node();
            f->value="term";
            f->children[0]=term(sc,query,stat);
            a->children[2]=f;
            f->childnum=1;
            stat=sc.scan(query);
            a->childnum=3;
        }
        return a;
    }
    
    Node* term(Scanner& sc,string query,string& stat)
    {
        if(stat!="\"" && stat!="\'")
        {
            if(isdigit(stat[0]))
            {
                Node* a=new Node();
                a->value="integer";
                Node* b=new Node();
                b->value=stat;
                b->childnum=0;
                a->children[0]=b;
                a->childnum=1;
                return a;
            }
            else
            {
                if(query[sc.showposition()]!='.')
                {
                    Node* a=new Node();
                    a->value="column_name";
                    Node* b=new Node();
                    b->value="attribute_name";
                    b->childnum=1;
                    Node* c=new Node();
                    c->value=stat;
                    c->childnum=0;
                    b->children[0]=c;
                    a->children[0]=b;
                    a->childnum=1;
                    return a;  
                }
                else
                {
                    Node* a=new Node();
                    a->value="column_name";
                    Node* b=new Node();
                    b->value="table_name";
                    b->childnum=1;
                    Node* c=new Node();
                    c->value=stat;
                    c->childnum=0;
                    b->children[0]=c;
                    a->children[0]=b;
                    stat=sc.scan(query);
                    stat=sc.scan(query);
                    Node* d=new Node();
                    d->value="attribute_name";
                    d->childnum=1;
                    Node* e=new Node();
                    e->value=stat;
                    e->childnum=0;
                    d->children[0]=e;
                    a->children[1]=d;  
                    a->childnum=2;
                    return a;
                }
            }
        }
        else
        {
            stat=sc.scan(query);
            Node* a=new Node();
            a->value="literal";
            Node* b=new Node();
            b->value=stat;
            b->childnum=0;
            a->children[0]=b;
            stat=sc.scan(query);
            a->childnum=1;
            return a;
        }
    }
};


