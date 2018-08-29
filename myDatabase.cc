//myDatabase allows you to read in a file and execute queries line by line.
//Or you can type in individual queries and type exit or EXIT to get out. 
#include <iostream>
#include <string>
#include <fstream>
#include "myExecution.h"
using namespace std;

void execuatequery(string query,SchemaManager& myschema_manager,MainMemory& mymem,RelationStat& myrelationstat)
{
    Parser a;
    ExecuteQuery b;
    Node* p=a.parse(query);
    if(p->children[0]->value=="CREATE") b.createrelation(p,myschema_manager,myrelationstat);
    if(p->children[0]->value=="DROP") b.droptable(p,myschema_manager);
    if(p->children[0]->value=="DELETE") b.deletetuples(p,myschema_manager,mymem,myrelationstat);
    if(p->children[0]->value=="INSERT") b.inserttuples(p,myschema_manager,mymem,myrelationstat);
    if(p->children[0]->value=="SELECT")
    {
        int newtuplenum=0;
        cout<<"----------"<<query<<"----------"<<endl;
        if(p->children[1]->value!="DISTINCT")
        {
            if(p->children[3]->childnum==1) b.selectstatement(p,myschema_manager,mymem,false,NULL,newtuplenum);
            else b.complexselectstat(p,myschema_manager,mymem,myrelationstat);
        }
        else
        {
            if(p->children[4]->childnum==1) b.selectstatement(p,myschema_manager,mymem,false,NULL,newtuplenum);
            else b.complexselectstat(p,myschema_manager,mymem,myrelationstat); 
        }
    }
}

int main()
{
    MainMemory mymem;
    Disk mydisk;
    SchemaManager myschema_manager(&mymem,&mydisk);
    RelationStat myrelationstat;
    mydisk.resetDiskIOs();
    mydisk.resetDiskTimer();
    clock_t start_time;
    start_time=clock();
    cout<<"Please type in a valid query or a file name:"<<endl;
    string query;
    getline(cin,query);
    Scanner assistant_scanner;
    string str=assistant_scanner.scan(query);
    if(str!="CREATE" && str!="DROP" && str!="SELECT" && str!="DELETE" && str!="INSERT")
    {
        ifstream file;
        const char* sub=query.c_str();
        file.open(sub,fstream::in);
        cout<<endl;
        if(file.is_open())
        {
            string singlequery;
            while(getline(file,singlequery))
            {
                Scanner newscanner;
                string verifyquery=newscanner.scan(singlequery);
                if(verifyquery=="CREATE" || verifyquery=="DROP" || verifyquery=="SELECT" || verifyquery=="DELETE" || verifyquery=="INSERT") 
                {
                    mydisk.resetDiskIOs();
                    execuatequery(singlequery,myschema_manager,mymem,myrelationstat);
                    cout<<"Disk I/Os: "<<mydisk.getDiskIOs()<<endl;
                }
            }
        }
        else
        {
            cout<<"File can't be opened. Please check the name of the file.";
        }
    }
    else
    {
        while(query!="exit" && query!="EXIT")
        {
            //Execuate single query typed by the user.
            execuatequery(query,myschema_manager,mymem,myrelationstat);
            cout<<"Please type in another valid query or \"exit\" to exit:";
            cout<<endl;
            getline(cin,query);
        }
    }
/*    string query="CREATE TABLE r(a STR20,b INT)";
    Parser a;
    Node* p=a.parse(query);
    ExecuteQuery b;
    b.createrelation(p,myschema_manager,myrelationstat);
    query="CREATE TABLE s(b INT,c INT)";
    Node* r=a.parse(query);
    b.createrelation(r,myschema_manager,myrelationstat);
    query="INSERT INTO r(a,b) VALUES (\"2\",5)";
    Node* ra=a.parse(query);
    b.inserttuples(ra,myschema_manager,mymem,myrelationstat);
    query="INSERT INTO r(a,b) VALUES (\"4\",5)";
    Node* rb=a.parse(query);
    b.inserttuples(rb,myschema_manager,mymem,myrelationstat);
    query="INSERT INTO s(b,c) VALUES (4,6)";
    Node* rab=a.parse(query);
    b.inserttuples(rab,myschema_manager,mymem,myrelationstat);
    query="INSERT INTO s(b,c) VALUES (5,7)";
    Node* rc=a.parse(query);
    b.inserttuples(rc,myschema_manager,mymem,myrelationstat);
    query="DELETE FROM r WHERE a=7";
    Node* rd=a.parse(query);
    b.deletetuples(rd,myschema_manager,mymem,myrelationstat);
    query="CREATE TABLE t(a STR20,c INT)";
    Node* re=a.parse(query);
    b.createrelation(re,myschema_manager,myrelationstat);
    query="INSERT INTO t(a,c) VALUES (\"4\",6)";
    Node* rh=a.parse(query);
    b.inserttuples(rh,myschema_manager,mymem,myrelationstat);
    query="INSERT INTO t(a,c) VALUES (\"4\",6)";
    Node* ri=a.parse(query);
    b.inserttuples(ri,myschema_manager,mymem,myrelationstat);
    query="INSERT INTO t(a,c) VALUES (\"2\",7)";
    Node* rj=a.parse(query);
    b.inserttuples(rj,myschema_manager,mymem,myrelationstat);   
    query="SELECT DISTINCT * FROM r,s WHERE r.b>s.b";
    Node* rf=a.parse(query);
    b.complexselectstat(rf,myschema_manager,mymem,myrelationstat);*/
/*    string query="CREATE TABLE r(a INT,b INT)";
    Parser a;
    Node* p=a.parse(query);
    ExecuteQuery b;
    b.createrelation(p,myschema_manager,myrelationstat);
    query="CREATE TABLE s(a INT,b INT)";
    Node* r=a.parse(query);
    b.createrelation(r,myschema_manager,myrelationstat);
    query="INSERT INTO r(a,b) VALUES (5,7)";
    Node* ra=a.parse(query);
    b.inserttuples(ra,myschema_manager,mymem,myrelationstat);
    query="INSERT INTO r(a,b) VALUES (5,5)";
    Node* rb=a.parse(query);
    b.inserttuples(rb,myschema_manager,mymem,myrelationstat);
    query="INSERT INTO s(a,b) VALUES (5,5)";
    Node* rab=a.parse(query);
    b.inserttuples(rab,myschema_manager,mymem,myrelationstat);
    query="SELECT DISTINCT * FROM r,s WHERE r.a=s.a AND r.b=s.b ORDER BY s.b";
    Node* rf=a.parse(query);
    b.complexselectstat(rf,myschema_manager,mymem,myrelationstat);*/
}