//This file generate a logical query plan according to the parse tree.
//Pushing selection and optimizing natural join is also handled.
//Class FieldStat contains information for estimating cost for each operation.
#include <iostream>
#include <string>
#include <vector>
#include <cstring>
#include <map>
#include <set>
#include <sstream>
#include <algorithm>
#include "myParser.h"
using namespace std;

class NaturalJoinGroup
{
public:
    vector<Node*> operands;
    vector<Node*> operandsinfo;
};

class FieldValues
{
public:
    map<string,int> field_values;
};

class FieldStat
{
public:

    FieldStat():tuplenum(0) {}
    FieldStat(Schema newschema):tuplenum(0)
    {
        for(int i=0;i<newschema.getNumOfFields();i++)
        {
            fieldname.push_back(newschema.getFieldNames()[i]);
            valuecount.push_back(0);
            FieldValues a;
            fieldvalues.push_back(a);
        }
    }
    
    int tuplenum;
    vector<string> fieldname;
    vector<int> valuecount;
    vector<FieldValues> fieldvalues;
    
    void reset(Schema newschema)
    {
        tuplenum=0;
        fieldname.clear();
        valuecount.clear();
        fieldvalues.clear();
        for(int i=0;i<newschema.getNumOfFields();i++)
        {
            fieldname.push_back(newschema.getFieldNames()[i]);
            valuecount.push_back(0);
            FieldValues a;
            fieldvalues.push_back(a);
        }        
    }
};

class RelationStat
{
public:

    map<string,int> relationnum;
    vector<FieldStat> statInfo;
    
    void createnewentry(string relationname,Schema newschema)
    {
        if(relationnum.find(relationname)==relationnum.end())
        {
            FieldStat a(newschema);
            statInfo.push_back(a);
            relationnum[relationname]=statInfo.size()-1;
        }
        else
        {
            statInfo[relationnum[relationname]].reset(newschema);
        }
    }
    
    void insertnewtuple(string relationname,vector<string> field_names,vector<string> field_values)
    {
        int num=relationnum[relationname];
        statInfo[num].tuplenum++;
        for(int i=0;i<statInfo[num].fieldname.size();i++)
        {
            for(int j=0;j<field_names.size();j++)
            {
                if(statInfo[num].fieldname[i]==field_names[j])
                {
                    if(field_values[j]!="NULL")
                    {
                        if(statInfo[num].fieldvalues[i].field_values.find(field_values[j])!=statInfo[num].fieldvalues[i].field_values.end())
                        {
                            statInfo[num].fieldvalues[i].field_values[field_values[j]]++;
                        }
                        else
                        {
                            statInfo[num].fieldvalues[i].field_values[field_values[j]]=1;
                            statInfo[num].valuecount[i]++;
                        }
                    }
                }
            }
        }
    }
    
    void deletealltuples(string relationname)
    {
        int num=relationnum[relationname];
        statInfo[num].tuplenum=0;
        for(int i=0;i<statInfo[num].valuecount.size();i++)
        {
            statInfo[num].valuecount[i]=0;
        }
        for(int i=0;i<statInfo[num].fieldvalues.size();i++)
        {
            statInfo[num].fieldvalues[i].field_values.clear();
        }
    }
    
    void deleteonetuple(string relationname,Tuple tuple)
    {
        Schema schema=tuple.getSchema();
        vector<enum FIELD_TYPE> field_types;
        field_types=schema.getFieldTypes();
        int num=relationnum[relationname];
        statInfo[num].tuplenum--;
        for(int i=0;i<statInfo[num].fieldname.size();i++)
        {
            string fieldvalue;
            stringstream buffer;
            if(field_types[i]==INT) 
            {
                buffer<<tuple.getField(i).integer;
                fieldvalue=buffer.str();
            }
            else fieldvalue=*(tuple.getField(i).str);
            if(fieldvalue!="0" && fieldvalue!="NULL")
            {
                statInfo[num].fieldvalues[i].field_values[fieldvalue]--;
                if(statInfo[num].fieldvalues[i].field_values[fieldvalue]==0)
                {
                    statInfo[num].fieldvalues[i].field_values.erase(fieldvalue);
                    statInfo[num].valuecount[i]--;
                }
            }
        }
    }
};

class SelectStatProcessor
{
public:
    
    SelectStatProcessor(): pushpoint(NULL)
    {
        for(int i=0;i<20;i++)
        {
            tableneeded[i]=0;
        }
        count=0;
    }
    
    Node* pushpoint;
    int tableneeded[20];
    int count;
    
    Node* logicalplan(Node* p)
    {
        Node* a=new Node();
        a->value="projection";
        Node* c=new Node();
        c->value="cross_join";
        if(p->children[1]->value!="DISTINCT")
        {
            int i=0;
            a->children[1]=p->children[1];
            c->childnum=get_table_list(c,p->children[3],i);
        }
        else
        {
            int i=0;
            a->children[1]=p->children[2];
            c->childnum=get_table_list(c,p->children[4],i);
        }
        Node* b=NULL;
        for(int i=0;i<p->childnum;i++)
        {
            if(p->children[i]->value=="WHERE")
            {
                b=new Node();
                b->value="selection";
                b->children[0]=c;
                b->children[1]=p->children[i+1];
                b->childnum=2;
            }
        }   
        if(b!=NULL) a->children[0]=b;
        else a->children[0]=c;
        a->childnum=2;
        return a;
    }
    
    void optimizelqp(Node* p,SchemaManager& myschema_manager,RelationStat& myrelationstat)  //not finished
    {
        if(p->children[0]->value=="selection")
        {
            Node* a=p->children[0]->children[1];
            while(a->childnum==3)
            {
                a=a->children[2];
            }
            a=a->children[0];
            if(a->childnum==3)
            {
                Node* b=a->children[2];
                a->children[1]=NULL;
                a->children[2]=NULL;
                a->childnum=1;
                while(b->childnum==3)
                {
                    Node* c=b;
                    while(c->children[2]->childnum==3)
                    {
                        c=c->children[2];
                    }
                    Node* d=c;
                    c=c->children[2];
                    d->children[1]=NULL;
                    d->children[2]=NULL;
                    d->childnum=1;
                    vector<string> tablelist;
                    get_involved_table(tablelist,c);
                    pushselection(p->children[0]->children[0],c,tablelist);
                }
                vector<string> tablelist;
                get_involved_table(tablelist,b);
                pushselection(p->children[0]->children[0],b,tablelist);
            }
            vector<string> tablelist;
            get_involved_table(tablelist,p->children[0]->children[1]);
            pushselection(p->children[0]->children[0],p->children[0]->children[1],tablelist);
            Node* tmp=p->children[0];
            //a deletion should be added here;
            p->children[0]=p->children[0]->children[0];
        }
        //If a cross join has more than two operands after selections have been pushed. Then make it into a left first tree.
        dissipatecross(p);
        naturaltocross(p,myschema_manager);
        physicalqueryplan(p,myrelationstat);
    }
    
    void dissipatecross(Node* p)
    {
        if(p->value=="cross_join")
        {
            int tmpchildnum=p->childnum;
            if(tmpchildnum>4)
            {
                Node* prenode=new Node();
                prenode->value="cross_join";
                for(int i=0;i<4;i++)
                {
                    prenode->children[i]=p->children[i];
                }
                prenode->childnum=4;
                for(int i=0;i<(tmpchildnum-6)/2;i++)
                {
                    Node* newnode=new Node();
                    newnode->value="cross_join";
                    newnode->children[0]=prenode;
                    Node* newtablelist=new Node();
                    newtablelist->value="table_in_sub";
                    int tablenamenum=0;
                    for(int j=0;j<prenode->children[1]->childnum;j++)
                    {
                        Node* tmptable=new Node();
                        tmptable->value=prenode->children[1]->children[j]->value;
                        tmptable->childnum=0;
                        newtablelist->children[tablenamenum++]=tmptable;
                    }
                    for(int j=0;j<prenode->children[3]->childnum;j++)
                    {
                        Node* tmptable=new Node();
                        tmptable->value=prenode->children[3]->children[j]->value;
                        tmptable->childnum=0;
                        newtablelist->children[tablenamenum++]=tmptable;
                    }
                    newtablelist->childnum=tablenamenum;
                    newnode->children[1]=newtablelist;
                    newnode->children[2]=p->children[2*i+4];
                    newnode->children[3]=p->children[2*i+5];
                    newnode->childnum=4;
                    prenode=newnode;
                }
                p->children[0]=prenode;
                Node* newtablelist=new Node();
                newtablelist->value="table_in_sub";
                int tablenamenum=0;
                for(int j=0;j<prenode->children[1]->childnum;j++)
                {
                    Node* tmptable=new Node();
                    tmptable->value=prenode->children[1]->children[j]->value;
                    tmptable->childnum=0;
                    newtablelist->children[tablenamenum++]=tmptable;
                }
                for(int j=0;j<prenode->children[3]->childnum;j++)
                {
                    Node* tmptable=new Node();
                    tmptable->value=prenode->children[3]->children[j]->value;
                    tmptable->childnum=0;
                    newtablelist->children[tablenamenum++]=tmptable;
                }
                newtablelist->childnum=tablenamenum;
                p->children[1]=newtablelist;
                p->children[2]=p->children[p->childnum-2];
                p->children[3]=p->children[p->childnum-1];
                for(int i=4;i<20;i++)
                {
                    p->children[i]=NULL;
                }
                p->childnum=4;
            }
        }
        for(int i=0;i<p->childnum;i++) dissipatecross(p->children[i]);
    }

    void physicalqueryplan(Node* p,RelationStat& myrelationstat)
    {
        estimatecost(p,myrelationstat);
        crosstotheta(p);
        vector<Node*> destination;
        vector<NaturalJoinGroup> group;
        groupnaturaljoin(p,destination,group);
        for(int i=0;i<group.size();i++)
        {
            dpnaturaljoin(p,destination[i],group[i]);
        }
    }
    
    void crosstotheta(Node* p)
    {
        if(p->value=="selection")
        {
            canbetheta(p);
        }
        for(int i=0;i<p->childnum;i++) crosstotheta(p->children[i]);
    }
    
    void canbetheta(Node* p)
    {
        Node* tmp=p;
        while(tmp->value=="selection") tmp=tmp->children[0];
        if(tmp->value=="cross_join")
        {
            int i=0;
            p->value="theta_join";
            p->children[4]=p->children[1];
            Node* tmp2=p->children[0];
            for(int j=0;j<tmp->childnum;j++) p->children[i++]=tmp->children[j];
            i++;
            while(tmp2->value=="selection") 
            {
                p->children[i++]=tmp2->children[1];
                tmp2=tmp2->children[0];
            }
            p->childnum=i;
        }
    }
    
    void dpnaturaljoin(Node* p,Node* destination,NaturalJoinGroup& singlegroup)
    {
        int** cost=new int* [singlegroup.operands.size()];
        for(int i=0;i<singlegroup.operands.size();i++) cost[i]=new int [1000]; //Therefore 12 relations is my largest limit.
        Node*** tmpnode=new Node** [singlegroup.operands.size()];
        for(int i=1;i<singlegroup.operands.size();i++)
        {
            tmpnode[i]=new Node* [1000];
            for(int j=0;j<1000;j++) tmpnode[i][j]=new Node();
        }
        tmpnode[0]=new Node* [1000];
        int count=0;
        for(int i=0;i<singlegroup.operands.size();i++)
        {
            tmpnode[0][i]=singlegroup.operands[i];
            cost[0][i]=0;
        }
        for(int i=0;i<singlegroup.operands.size()-1;i++)
        {
            for(int j=i+1;j<singlegroup.operands.size();j++)
            {
                tmpnode[1][count]->children[0]=singlegroup.operands[i];
                tmpnode[1][count]->children[1]=singlegroup.operandsinfo[i];
                tmpnode[1][count]->children[2]=singlegroup.operands[j];
                tmpnode[1][count]->children[3]=singlegroup.operandsinfo[j];
                tmpnode[1][count]->childnum=4;
                tmpnode[1][count]->value="natural_join";
                estimatenatural(tmpnode[1][count]);
                cost[1][count]=0;
                count++;
            }
        }
        for(int i=3;i<=singlegroup.operands.size();i++)
        {
            vector<int> combination;
            int itemnum=singlegroup.operands.size();
            int num=1;
            int order=0;
            for(int k=0;k<=itemnum-i;k++)
            {
                combination.push_back(k);
                testallcombination(i,itemnum,combination,num,order,tmpnode,cost);
                combination.pop_back();
            }
        }
        vector<Node*> usefultmpnode;
        getusefultmpnode(tmpnode[singlegroup.operands.size()-1][0],usefultmpnode);
        for(int i=1;i<singlegroup.operands.size();i++)
        {
            for(int j=0;j<1000;j++)
            {
                bool tmpnodeuseful=false;
                for(int k=0;k<usefultmpnode.size();k++)
                {
                    if(tmpnode[i][j]==usefultmpnode[k]) tmpnodeuseful=true;
                }
                if(!tmpnodeuseful) delete tmpnode[i][j];
            }
            delete tmpnode[i];
            delete cost[i];
        }
        delete tmpnode;
        delete cost[0];
        delete cost;
        Node* predestination;
        int destinationnum;
        locatedestination(p,destination,predestination,destinationnum);
        predestination->children[destinationnum]=usefultmpnode[0];
    }
    
    void locatedestination(Node* p,Node* destination,Node*& predestination,int& destinationnum)
    {
        for(int i=0;i<p->childnum;i++)
        {
            if(p->children[i]==destination)
            {
                predestination=p;
                destinationnum=i;
            }
        }
        for(int i=0;i<p->childnum;i++)
        {
            locatedestination(p->children[i],destination,predestination,destinationnum);
        }
    }
    
    void getusefultmpnode(Node* p,vector<Node*>& usefultmpnode)
    {
        if(p->value!="natural_join") return;
        else
        {
            usefultmpnode.push_back(p);
            if(p->children[1]==NULL)
            {
                Node* pa=new Node();
                pa->childnum=0;
                pa->value="table_in_sub";
                Node* pb=new Node();
                pb->childnum=0;
                pb->value="table_in_sub";
                p->children[1]=pa;
                p->children[3]=pb;
            }
        }
        getusefultmpnode(p->children[0],usefultmpnode);
        getusefultmpnode(p->children[2],usefultmpnode);
    }
    
    void testallcombination(int i,int itemnum,vector<int> combination,int num,int& order,Node***& tmpnode,int**& cost)
    {
        if(combination.size()==i)
        {
            cost[i-1][order]=100000000;
            findmincost(i,order,combination,tmpnode,cost,itemnum);
            order++;
            return;
        }
        for(int j=combination.back()+1;j<=itemnum-i+num;j++)
        {
            combination.push_back(j);
            num++;
            testallcombination(i,itemnum,combination,num,order,tmpnode,cost);
            combination.pop_back();
            num--;
        }
    }
    
    void findmincost(int i,int order,vector<int>& combination,Node***& tmpnode,int**& cost,int itemnum)
    {
        for(int j=1;j<=i/2;j++)
        {
            vector<int> partition;
            int num=1;
            for(int k=0;k<=i-j;k++)
            {
                partition.push_back(k);
                checkpartitions(i,order,combination,tmpnode,cost,partition,j,num,itemnum);
                partition.pop_back();
            }
        }
    }
    
    void checkpartitions(int i,int order,vector<int>& combination, Node***& tmpnode,int**& cost,vector<int> partition,int j,int num,int itemnum)
    {
        if(partition.size()==j)
        {
            int ia=0;
            int ib=0;
            vector<int> partition2;
            while(ia<combination.size())
            {
                if(ia!=partition[ib])
                {
                    partition2.push_back(ia);
                }
                else
                {
                    ib++;
                }
                ia++;
            }
            for(int l=0;l<partition.size();l++) partition[l]=combination[partition[l]];
            vector<int> tmpcombination;
            int order1;
            int tmporder=0;
            int tmpnum=1;
            for(int l=0;l<=itemnum-j;l++)
            {
                tmpcombination.push_back(l);
                getorder(j,itemnum,tmpcombination,tmpnum,tmporder,partition,order1);
                tmpcombination.pop_back();
            }
            int order2;
            tmporder=0;
            tmpnum=1;
            for(int l=0;l<=itemnum-j;l++)
            {
                tmpcombination.push_back(l);
                getorder(combination.size()-j,itemnum,tmpcombination,tmpnum,tmporder,partition2,order2);
                tmpcombination.pop_back();
            }
            int tmpcost=tmpnode[j-1][order1]->tuplenum+cost[j-1][order1]+tmpnode[combination.size()-j-1][order2]->tuplenum+cost[combination.size()-j-1][order2];
            if(cost[i-1][order]>tmpcost)
            {
                tmpnode[i-1][order]->children[0]=tmpnode[j-1][order1];
                tmpnode[i-1][order]->children[2]=tmpnode[combination.size()-j-1][order2];
                tmpnode[i-1][order]->childnum=4;
                tmpnode[i-1][order]->value="natural_join";
                tmpnode[i-1][order]->involvedtable.clear();
                tmpnode[i-1][order]->fieldname.clear();
                tmpnode[i-1][order]->valuecount.clear();                
                estimatenatural(tmpnode[i-1][order]);
            }
            return;
        }
        for(int k=partition.back()+1;k<=i-j+num;k++)
        {
            combination.push_back(k);
            num++;
            checkpartitions(i,order,combination,tmpnode,cost,partition,j,num,itemnum);
            combination.pop_back();
            num--;
        }
    }
    
    void getorder(int j,int itemnum,vector<int> tmpcombination,int tmpnum,int& tmporder,vector<int>& partition,int& order1)
    {
        if(tmpcombination.size()==j)
        {
            bool partitionmatch=true;
            for(int l=0;l<partition.size();l++)
            {
                if(tmpcombination[l]!=partition[l]) partitionmatch=false;
            }
            if(partitionmatch) order1=tmporder;
            tmporder++;
            return;
        }
        for(int k=tmpcombination.back()+1;k<=itemnum-j+tmpnum;k++)
        {
            tmpcombination.push_back(k);
            tmpnum++;
            getorder(j,itemnum,tmpcombination,tmpnum,tmporder,partition,order1);
            tmpcombination.pop_back();
            tmpnum--;
        }
    }
    
    void groupnaturaljoin(Node* p,vector<Node*>& destination,vector<NaturalJoinGroup>& group) //Deletion should be properly added here. But it's a little trick, so I didn't get a chance to do it.
    {
        if(p->value=="natural_join")  //Suppose natural_join only has two operand. It should be true.
        {
            if(p->children[0]->value=="natural_join" || p->children[2]->value=="natural_join")
            {
                destination.push_back(p);
                NaturalJoinGroup singlegroup;                
                singlenaturaljoingroup(p,destination,group,singlegroup);
                group.push_back(singlegroup);
            }
            else 
            {
                groupnaturaljoin(p->children[0],destination,group);
                groupnaturaljoin(p->children[2],destination,group);
            }
        }
        else 
        {
            for(int i=0;i<p->childnum;i++) groupnaturaljoin(p->children[i],destination,group);
        }
    }
    
    void singlenaturaljoingroup(Node* p,vector<Node*>& destination,vector<NaturalJoinGroup>& group,NaturalJoinGroup& singlegroup)
    {
        
        if(p->children[0]->value!="natural_join")
        {
            singlegroup.operands.push_back(p->children[0]);
            singlegroup.operandsinfo.push_back(p->children[1]);
            groupnaturaljoin(p->children[0],destination,group);
        }
        else
        {
            singlenaturaljoingroup(p->children[0],destination,group,singlegroup);            
        }
        if(p->children[2]->value!="natural_join")
        {
            singlegroup.operands.push_back(p->children[2]);
            singlegroup.operandsinfo.push_back(p->children[3]);
            groupnaturaljoin(p->children[2],destination,group);
        }
        else
        {
            singlenaturaljoingroup(p->children[2],destination,group,singlegroup);            
        }
    }
    
    void estimatecost(Node* p,RelationStat& myrelationstat)
    {
        if(p->value=="table_in_sub") return;
        if(p->value=="select_list") return;        
        for(int i=0;i<p->childnum;i++) estimatecost(p->children[i],myrelationstat);
        if(p->value=="projection") estimateprojection(p);
        if(p->value=="selection") estimateselection(p);
        if(p->value=="cross_join") estimatecross(p);
        if(p->value=="natural_join") estimatenatural(p);
        if(p->value!="projection" && p->value!="selection" && p->value!="cross_join" && p->value!="natural_join") relationinfo(p,myrelationstat);
    }
    
    void relationinfo(Node* p,RelationStat& myrelationstat)
    {
        if(p->value=="select_list") return;
        int num=myrelationstat.relationnum[p->value];
        p->tuplenum=myrelationstat.statInfo[num].tuplenum;
        p->fieldname=myrelationstat.statInfo[num].fieldname;
        p->valuecount=myrelationstat.statInfo[num].valuecount;
        for(int i=0;i<myrelationstat.statInfo[num].fieldname.size();i++)
        {
            p->involvedtable.push_back(p->value);
        }
    }
    
    void estimateprojection(Node* p)
    {
        p->tuplenum=p->children[0]->tuplenum;
        if(p->children[1]->children[0]->value=="*")
        {
            p->involvedtable=p->children[0]->involvedtable;
            p->fieldname=p->children[0]->fieldname;
            p->valuecount=p->children[0]->valuecount;
        }
        else
        {
            vector<string> tablenames;
            vector<string> attrnames;
            getselectinfo(p->children[1],tablenames,attrnames,p->children[0]->involvedtable[0]);
            for(int i=0;i<tablenames.size();i++)
            {
                bool completematch=false;
                for(int j=0;j<p->children[0]->fieldname.size();j++)
                {
                    if(tablenames[i]==p->children[0]->involvedtable[j] && attrnames[i]==p->children[0]->fieldname[j])
                    {
                        completematch=true;
                        p->involvedtable.push_back(p->children[0]->involvedtable[j]);
                        p->fieldname.push_back(p->children[0]->fieldname[j]);
                        p->valuecount.push_back(p->children[0]->valuecount[j]);
                    }
                }
                if(!completematch)
                {
                    for(int j=0;j<p->children[0]->fieldname.size();j++)
                    //It can't cover all the cases. For example, if there are three common attributes in three tables and two of them are equaled, there will be two left.
                    //We need to have the history to tell the one we want.
                    {
                        if(attrnames[i]==p->children[0]->fieldname[j])
                        {
                            p->involvedtable.push_back(tablenames[i]);
                            p->fieldname.push_back(p->children[0]->fieldname[j]);
                            p->valuecount.push_back(p->children[0]->valuecount[j]); 
                        }
                    }
                }
            }
        }
    }
    
    void getselectinfo(Node* p,vector<string>& tablenames,vector<string>& attrnames,string assistname)
    {
        if(p->value=="column_name")
        {
            if(p->childnum==1)
            {
                tablenames.push_back(assistname);
                attrnames.push_back(p->children[0]->children[0]->value);
            }
            else
            {
                tablenames.push_back(p->children[0]->children[0]->value);
                attrnames.push_back(p->children[1]->children[0]->value);
            }
        }
        for(int i=0;i<p->childnum;i++) getselectinfo(p->children[i],tablenames,attrnames,assistname);
    }
    
    void estimateselection(Node* p)  //This function doesn't take those selections in which two relations are involved and it's not a equality check.
    {
        bool isequal=false;
        checkitsequal(p->children[1],isequal);
        vector<string> tablenames;
        vector<string> attrnames;
        getselectinfo(p->children[1],tablenames,attrnames,"N/A");
        if(tablenames.size()<2)
        {
            if(isequal)
            {
                int valuenum;
                p->involvedtable=p->children[0]->involvedtable;
                p->fieldname=p->children[0]->fieldname;
                for(int i=0;i<p->children[0]->involvedtable.size();i++)
                {
                    if(tablenames[0]==p->children[0]->involvedtable[i] && attrnames[0]==p->children[0]->fieldname[i])
                    {
                        p->valuecount.push_back(1);
                        valuenum=p->children[0]->valuecount[i];
                    }
                    else p->valuecount.push_back(p->children[0]->valuecount[i]);
                } 
                p->tuplenum=(p->children[0]->tuplenum)/valuenum;                
            }
            else
            {
                p->tuplenum=(p->children[0]->tuplenum)/3;
                p->involvedtable=p->children[0]->involvedtable;
                p->fieldname=p->children[0]->fieldname;
                for(int i=0;i<p->children[0]->involvedtable.size();i++)
                {
                    if(tablenames[0]==p->children[0]->involvedtable[i] && attrnames[0]==p->children[0]->fieldname[i])
                    {
                        p->valuecount.push_back(p->children[0]->valuecount[i]/3);
                    }
                    else p->valuecount.push_back(p->children[0]->valuecount[i]);
                }
            }
        }
        else
        {
            if(isequal)
            {
                int abandonedfield=p->children[0]->involvedtable.size();
                for(int i=0;i<p->children[0]->involvedtable.size();i++)
                {
                    if(i!=abandonedfield)
                    {
                        bool matchfound=false;
                        for(int j=0;j<p->children[0]->involvedtable.size();j++)
                        {
                            if(tablenames[0]==p->children[0]->involvedtable[i] && attrnames[0]==p->children[0]->fieldname[i] && tablenames[1]==p->children[0]->involvedtable[j] && attrnames[1]==p->children[0]->fieldname[j])
                            {
                                p->tuplenum=(p->children[0]->childnum)/max(p->children[0]->valuecount[i],p->children[0]->valuecount[j]);
                                p->involvedtable.push_back(p->children[0]->involvedtable[i]);
                                p->fieldname.push_back(p->children[0]->fieldname[i]);
                                p->valuecount.push_back(min(p->children[0]->valuecount[i],p->children[0]->valuecount[j]));
                                abandonedfield=j;
                                matchfound=true;
                            }
                        }
                        if(!matchfound)
                        {
                            p->involvedtable.push_back(p->children[0]->involvedtable[i]);
                            p->fieldname.push_back(p->children[0]->fieldname[i]);
                            p->valuecount.push_back(p->children[0]->valuecount[i]);                        
                        }
                    }
                }
            }
            else
            {
                //Not really sure how to estimatecost if an unequal condition involving two tables appears.
                for(int i=0;i<p->children[0]->involvedtable.size();i++)
                {
                    bool matchfound=false;
                    for(int j=0;j<p->children[0]->involvedtable.size();j++)
                    {
                        if(tablenames[0]==p->children[0]->involvedtable[i] && attrnames[0]==p->children[0]->fieldname[i] && tablenames[1]==p->children[0]->involvedtable[j] && attrnames[1]==p->children[0]->fieldname[j])
                        {
                            p->tuplenum=(p->children[0]->childnum)/max(p->children[0]->valuecount[i],p->children[0]->valuecount[j]);
                            p->involvedtable.push_back(p->children[0]->involvedtable[i]);
                            p->fieldname.push_back(p->children[0]->fieldname[i]);
                            p->valuecount.push_back(min(p->children[0]->valuecount[i],p->children[0]->valuecount[j]));
                            matchfound=true;
                        }
                    }
                    if(!matchfound)
                    {
                        p->involvedtable.push_back(p->children[0]->involvedtable[i]);
                        p->fieldname.push_back(p->children[0]->fieldname[i]);
                        p->valuecount.push_back(p->children[0]->valuecount[i]);                        
                    }

                }                                       
            }
        }
    }
    
    
    void checkitsequal(Node* p,bool& isequal)
    {
        if(p->value=="comp_op")
        {
            if(p->children[0]->value=="=") isequal=true;
        }
        for(int i=0;i<p->childnum;i++) checkitsequal(p->children[i],isequal);
    }
    
    void estimatecross(Node* p)
    {
        p->tuplenum=1;
        for(int i=0;i<p->childnum/2;i++) p->tuplenum*=p->children[2*i]->tuplenum;
        for(int i=0;i<p->childnum/2;i++)
        {
            for(int j=0;j<p->children[2*i]->involvedtable.size();j++)
            {
                p->involvedtable.push_back(p->children[2*i]->involvedtable[j]);
                p->fieldname.push_back(p->children[2*i]->fieldname[j]);
                p->valuecount.push_back(p->children[2*i]->valuecount[j]);
            }
        }
    }
    
    void estimatenatural(Node* p)
    {
        int maxmultiply=1;
        for(int i=0;i<p->children[0]->involvedtable.size();i++)
        {
            bool matchfound=false;            
            for(int j=0;j<p->children[2]->involvedtable.size();j++)
            {
                if(p->children[0]->fieldname[i]==p->children[2]->fieldname[j])
                {
                    matchfound=true;
                    p->involvedtable.push_back(p->children[0]->involvedtable[i]);
                    p->fieldname.push_back(p->children[0]->fieldname[i]);
                    p->valuecount.push_back(min(p->children[0]->valuecount[i],p->children[2]->valuecount[j]));
                    maxmultiply*=max(p->children[0]->valuecount[i],p->children[2]->valuecount[j]);
                }
            }
            if(!matchfound)
            {
                p->involvedtable.push_back(p->children[0]->involvedtable[i]);
                p->fieldname.push_back(p->children[0]->fieldname[i]);
                p->valuecount.push_back(p->children[0]->valuecount[i]);               
            }
        }
        for(int i=0;i<p->children[2]->involvedtable.size();i++)
        {
            bool matchfound=false;            
            for(int j=0;j<p->children[0]->involvedtable.size();j++)
            {
                if(p->children[0]->fieldname[j]==p->children[2]->fieldname[i])
                {
                    matchfound=true;
                }
            }
            if(!matchfound)
            {
                p->involvedtable.push_back(p->children[2]->involvedtable[i]);
                p->fieldname.push_back(p->children[2]->fieldname[i]);
                p->valuecount.push_back(p->children[2]->valuecount[i]);               
            }
        }
        p->tuplenum=(p->children[0]->tuplenum)*(p->children[2]->tuplenum)/maxmultiply;
        if(p->tuplenum==0) p->tuplenum=1;
    }
    
    void naturaltocross(Node* p,SchemaManager& myschema_manager)
    {
        if(p->value=="cross_join" || p->value=="projection" || p->value=="natural_join")
        {
            for(int i=0;i<p->childnum;i++)
            {
                if(p->children[i]->value=="selection" || p->children[i]->value=="cross_join") 
                {
                    canbenatural(p,myschema_manager,i);
                }
            }
        }
        if(p->value=="select_list") return;
        for(int i=0;i<p->childnum;i++)  naturaltocross(p->children[i],myschema_manager);
    }
    
    void canbenatural(Node *pp,SchemaManager& myschema_manager,int child)
    {
        Node* p=pp->children[child];
        vector<string> equaledattr;
        vector<Node*> equaledcondition;
        Node* q=p;
        while(p->value=="selection")
        {
            if(p->children[1]->value!="search_condition" || p->children[1]->childnum==1)
            {
                if(getequaledattr(p,equaledattr))
                {
                       equaledcondition.push_back(p);   //Need to only remove these p;
                }
            }
            p=p->children[0];
        }
        if(p->value=="cross_join" && p->childnum==4)
        {
            vector<string> commonattr;
            vector<int> leftnum;
            vector<int> rightnum;
            getcommonattr(p,commonattr,leftnum,rightnum,myschema_manager);
            bool allownaturaljoin=true;
            for(int i=0;i<leftnum.size();i++)
            {
                if(leftnum[i]!=1) alreadyjoined(allownaturaljoin);
                if(rightnum[i]!=1) alreadyjoined(allownaturaljoin);
            }
            if(allownaturaljoin)
            {
                if(commonattr.size()==equaledattr.size())
                {
                    int j=0;
                    while(j<equaledcondition.size() && equaledcondition[j]==pp->children[child])
                    {
                        Node* tmp=pp->children[child];
                        pp->children[child]=pp->children[child]->children[0];
                        tmp->children[0]=NULL;
                        tmp->children[1]=NULL;
                        //Deletion should be added here.
                        j++;
                    }
                    pp=pp->children[child];
                    while(j<equaledcondition.size() && pp->children[0]->value!="cross_join")
                    {
                        if(pp->children[0]==equaledcondition[j])
                        {
                            Node* tmp=pp->children[0];
                            pp->children[0]=pp->children[0]->children[0];
                            tmp->children[0]=NULL;
                            tmp->children[1]=NULL;
                            //Deletion should be added here.
                            j++;
                        }
                        pp=pp->children[0];
                    }
                    pp->value="natural_join";
                }
            }
        }
    }
    
    void alreadyjoined(bool& allownaturaljoin) //Should be implemented afterwards.
    {
        allownaturaljoin=true;
    }
    
    void getcommonattr(Node* p,vector<string>& commonattr,vector<int>& leftnum,vector<int>& rightnum,SchemaManager& myschema_manager)
    {
        vector<string> leftattr;
        vector<string> rightattr;
        vector<int> tmpleftnum;
        vector<int> tmprightnum;
        Node* q=p->children[1];
        for(int i=0;i<q->childnum;i++)
        {
            vector<string> tmpattr=myschema_manager.getRelation(q->children[i]->value)->getSchema().getFieldNames();
            for(int j=0;j<tmpattr.size();j++)
            {
                bool exist=false;
                for(int k=0;k<leftattr.size();k++)
                {
                    if(tmpattr[j]==leftattr[k])
                    {
                        exist=true;
                        tmpleftnum[k]++;
                    }
                }
                if(!exist)
                {
                    leftattr.push_back(tmpattr[j]);
                    tmpleftnum.push_back(1);
                }
            }
        }
        Node* r=p->children[3];
        for(int i=0;i<r->childnum;i++)
        {
            vector<string> tmpattr=myschema_manager.getRelation(r->children[i]->value)->getSchema().getFieldNames();
            for(int j=0;j<tmpattr.size();j++)
            {
                bool exist=false;
                for(int k=0;k<rightattr.size();k++)
                {
                    if(tmpattr[j]==rightattr[k])
                    {
                        exist=true;
                        tmprightnum[k]++;
                    }
                }
                if(!exist)
                {
                    rightattr.push_back(tmpattr[j]);
                    tmprightnum.push_back(1);
                }
            }
        }
        for(int i=0;i<leftattr.size();i++)
        {
            for(int j=0;j<rightattr.size();j++)
            {
                if(leftattr[i]==rightattr[j])
                {
                    commonattr.push_back(leftattr[i]);
                    leftnum.push_back(tmpleftnum[i]);
                    rightnum.push_back(tmprightnum[i]);
                }
            }
        }
    }
    
    bool getequaledattr(Node* p,vector<string>& equaledattr)
    {
        bool isequal=false;
        string attrinvolved="N/A";
        itissetequal(p,isequal,attrinvolved);
        if(isequal)
        {
            equaledattr.push_back(attrinvolved);
            return isequal;
        }
        return isequal;
    }
    
    void itissetequal(Node* p,bool& isequal,string& attrinvolved)
    {
        if(p->value=="boolean_factor")
        {
            string leftattr=getattr(p->children[0]);
            string rightattr=getattr(p->children[2]);
            if(p->children[1]->children[0]->value=="=" && leftattr==rightattr && leftattr!="N/A")
            {
                isequal=true;
                attrinvolved=leftattr;
            }
            return;
        }
        for(int i=0;i<p->childnum;i++)  itissetequal(p->children[i],isequal,attrinvolved);
    }
    
    string getattr(Node* p)
    {
        if(p->childnum==3) return "N/A";
        string res="N/A";
        searchforattr(p,res);
        return res;
    }
    
    void searchforattr(Node* p,string& res)
    {
        if(p->value=="attribute_name")
        {
            res=p->children[0]->value;
            return;
        }
        for(int i=0;i<p->childnum;i++)  searchforattr(p->children[i],res);
    }
    
    void pushselection(Node* p,Node* q,vector<string> tablelist)    
    {
        if(tablelist.size()>1)
        {
            pushto(p,tablelist);
            if(count<((pushpoint->childnum)/2))
            {
                Node* a=new Node();
                Node* b=new Node();
                b->value="selection";
                b->childnum=2;
                b->children[1]=q;
                Node* c=new Node();
                c->value="cross_join";
                b->children[0]=c;
                a->value="table_in_sub";
                int k=0;
                int l=0;
                for(int i=0;i<20;i++)
                {
                    if(tableneeded[i]==1)
                    {
                        for(int j=0;j<pushpoint->children[i+1]->childnum;j++)
                        {
                            Node* d=new Node();
                            a->children[k++]=d;
                            d->value=pushpoint->children[i+1]->children[j]->value;
                            d->childnum=0;
                        }
                        c->children[l++]=pushpoint->children[i];
                        c->children[l++]=pushpoint->children[i+1];
                        pushpoint->children[i]=NULL;
                        pushpoint->children[i+1]=NULL;
                    }
                }
                c->childnum=l;
                a->childnum=k;
                int m=0;
                int n=0;
                while(m<pushpoint->childnum)
                {
                    while(pushpoint->children[m]==NULL && m<pushpoint->childnum) 
                    {
                        m++;
                    }
                    if(pushpoint->children[m]!=NULL)    pushpoint->children[n++]=pushpoint->children[m++];
                }
                pushpoint->children[n++]=b;
                pushpoint->children[n++]=a;
                pushpoint->childnum=n;
                for(int i=n;i<20;i++)
                {
                    pushpoint->children[i]=NULL;
                }
            }
            else
            {
                Node* a=new Node();
                a->value="cross_join";
                for(int i=0;i<pushpoint->childnum;i++)
                {
                    a->children[i]=pushpoint->children[i];
                }
                a->childnum=pushpoint->childnum;
                pushpoint->value="selection";
                for(int i=0;i<pushpoint->childnum;i++)
                {
                    pushpoint->children[i]=NULL;
                }
                pushpoint->children[0]=a;
                pushpoint->children[1]=q;
                pushpoint->childnum=2;
            }
        }
        else
        {
            pushtosingletable(p,tablelist[0]);
            Node* a=new Node();
            a->value=tablelist[0];
            a->childnum=0;
            pushpoint->value="selection";
            pushpoint->children[0]=a;
            pushpoint->children[1]=q;
            pushpoint->childnum=2;
        }
    }
    
    void pushtosingletable(Node* p,string table)
    {
        if(p->value=="table_in_sub" || p->value=="table_name") return;
        if(p->value==table && p->childnum==0) 
        {
            pushpoint=p;
        }
        for(int i=0;i<p->childnum;i++) pushtosingletable(p->children[i],table);
    }
    
    void pushto(Node* p,vector<string> tablelist)
    {
        if(p->value=="cross_join")
        {
            if(pushstophere(p,tablelist))
            {
                pushpoint=p;
                return;
            }
        }
        for(int i=0;i<p->childnum;i++)
        {
            if(p->children[i]->value!="table_in_sub")   pushto(p->children[i],tablelist);
        }
    }
    
    bool pushstophere(Node* p,vector<string> tablelist)
    {
        for(int i=0;i<20;i++)
        {
            tableneeded[i]=0;
        }
        for(int i=1;i<p->childnum;i=i+2)
        {
            int size=tablelist.size();
            for(int j=0;j<size;j++)
            {
                for(int k=0;k<p->children[i]->childnum;k++)
                {
                    if(tablelist[j]==p->children[i]->children[k]->value)    tableneeded[i-1]=1;
                }
            }
        }
        count=0;
        for(int i=0;i<20;i++)
        {
            if(tableneeded[i]==1) count++;
        }
        if(count>1) return true;
        return false;
    }
    
    void get_involved_table(vector<string>& tablelist,Node* c)
    {
        if(c->value=="table_name")
        {
            tablelist.push_back(c->children[0]->value);
            return;
        }
        for(int i=0;i<c->childnum;i++)
        {
            get_involved_table(tablelist,c->children[i]);
        }
    }
    
    int get_table_list(Node* a,Node* b,int& i)
    {
        if(b->value=="table_list")
        {
            for(int j=0;j<b->childnum;j++)
            {
                get_table_list(a,b->children[j],i);
            }
        }
        if(b->value=="table_name")
        {
            Node* c=new Node();
            Node* d=new Node();
            Node* e=new Node();
            a->children[i++]=c;
            c->value=b->children[0]->value;
            c->childnum=0;
            a->children[i++]=d;
            d->value="table_in_sub";
            d->childnum=1;
            d->children[0]=e;
            e->value=b->children[0]->value;
            e->childnum=0;
        }
        return i;
    }
};
