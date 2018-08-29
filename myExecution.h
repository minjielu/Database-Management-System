//This file contains class to execute queries after a parse tree or a physical query plan is generated.
//One pass algorithm is implemented for projection,selection,cross join,theta join,duplicate elimination and sorting. Nested loop algorithm
//is implemented for cross and theta join. Two pass sorting based algorithm is applied for natural join, duplicate elimination and sorting.
#include<iostream>
#include<iterator>
#include<cstdlib>
#include<ctime>
#include<string>
#include "Block.h"
#include "Config.h"
#include "Disk.h"
#include "Field.h"
#include "MainMemory.h"
#include "Relation.h"
#include "Schema.h"
#include "SchemaManager.h"
#include "Tuple.h"
#include "myOptimization.h"

void appendTupleToRelation(Relation* relation_ptr, MainMemory& mem, int memory_block_index, Tuple& tuple) {
  Block* block_ptr;
  if (relation_ptr->getNumOfBlocks()==0) {
    block_ptr=mem.getBlock(memory_block_index);
    block_ptr->clear(); //clear the block
    block_ptr->appendTuple(tuple); // append the tuple
    relation_ptr->setBlock(relation_ptr->getNumOfBlocks(),memory_block_index);
  } else {
    relation_ptr->getBlock(relation_ptr->getNumOfBlocks()-1,memory_block_index);
    block_ptr=mem.getBlock(memory_block_index);

    if (block_ptr->isFull()) {
      block_ptr->clear(); //clear the block
      block_ptr->appendTuple(tuple); // append the tuple
      relation_ptr->setBlock(relation_ptr->getNumOfBlocks(),memory_block_index); //write back to the relation
    } else {
      block_ptr->appendTuple(tuple); // append the tuple
      relation_ptr->setBlock(relation_ptr->getNumOfBlocks()-1,memory_block_index); //write back to the relation
    }
  }  
}

class ExecuteQuery
{
public:
    Relation* createrelation(Node* p,SchemaManager& myschema_manager,RelationStat& myrelationstat)
    {
        vector<string> field_names;
        vector<enum FIELD_TYPE> field_types;
        mygetschema(field_names,field_types,p->children[3]);
        Schema schema(field_names,field_types);
        Relation* relation_ptr=myschema_manager.createRelation(p->children[2]->children[0]->value,schema);
        myrelationstat.createnewentry(p->children[2]->children[0]->value,schema);
        cout<<"----------Table "<<p->children[2]->children[0]->value<<" is created.----------"<<endl;
        return relation_ptr;
    }
    
    void droptable(Node* p,SchemaManager& myschema_manager)
    {
        Relation* tmprelation=myschema_manager.getRelation(p->children[2]->children[0]->value);
        if(tmprelation->getNumOfBlocks()!=0) tmprelation->deleteBlocks(0);
        myschema_manager.deleteRelation(p->children[2]->children[0]->value);
        cout<<"----------Table "<<p->children[2]->children[0]->value<<" is dropped.----------"<<endl;
    }
    
    void deletetuples(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,RelationStat& myrelationstat)
    {
        if(p->children[3]==NULL)
        {
            Relation* q=myschema_manager.getRelation(p->children[2]->children[0]->value);
            q->deleteBlocks(0);
            myrelationstat.deletealltuples(p->children[2]->children[0]->value);
            cout<<"----------ALL tuples in table "<<p->children[2]->children[0]->value<<" are deleted.----------"<<endl;
        }
        else
        {
            int deletecount=0;
            Relation* q=myschema_manager.getRelation(p->children[2]->children[0]->value);
            for(int i=0;i<q->getNumOfBlocks();i++)
            {
                bool blockchanged=false;
                q->getBlock(i,1);
                Block* block_ptr=mymem.getBlock(1);
                Schema myschema=q->getSchema();
                for(int j=0;j<myschema.getTuplesPerBlock();j++)
                {
                    Tuple tuple=block_ptr->getTuple(j);
                    if(!tuple.isNull())
                    {
                        if(satisfycondition(tuple,p->children[4],false,NULL,myschema_manager))
                        {
                            deletecount++;
                            myrelationstat.deleteonetuple(p->children[2]->children[0]->value,block_ptr->getTuple(j));                            
                            block_ptr->nullTuple(j);
                            blockchanged=true;
                        }
                    }
                }
                if(blockchanged) q->setBlock(i,1);
                block_ptr->clear();
            }
            if(deletecount==0) cout<<"----------No tuple in table "<<p->children[2]->children[0]->value<<" is deleted.----------"<<endl;
            else
            {
                if(deletecount==1) cout<<"----------One tuple in table "<<p->children[2]->children[0]->value<<" is deleted.----------"<<endl;
                else cout<<"----------"<<deletecount<<" tuples in table "<<p->children[2]->children[0]->value<<" are deleted.----------"<<endl;
            }
        }
    }
    
    void complexselectstat(Node* p,SchemaManager myschema_manager,MainMemory& mymem,RelationStat myrelationstat)
    {
        for(int i=0;i<10;i++)
        {
            Block* cleanallblock=mymem.getBlock(i);
            cleanallblock->clear();
        }
        SelectStatProcessor a;
        Node* q=a.logicalplan(p);
        a.optimizelqp(q,myschema_manager,myrelationstat);
        Node* prenode;
        int intermediatenum=0;
        locaterelations(q,myschema_manager);
        execuateselectquery(q,myschema_manager,mymem,prenode,intermediatenum,true);
        int position;
        if(q->memfront) position=2;
        else position=6;
        //Need to pick out distinct tuples.
        Node* pa=NULL;
        if(p->children[1]->value=="DISTINCT")
        {
            pa=new Node();
            pa->value="duplicate_elimination";
            pa->children[0]=q;
            pa->childnum=1;
            eliminateduplicate(pa,myschema_manager,mymem,intermediatenum);
        }
        bool needsort=false;
        Node* pb=NULL;
        for(int i=0;i<p->childnum;i++)
        {
            if(p->children[i]->value=="ORDER")
            {
                needsort=true;
                pb=p->children[i+2];
            }
        }
        //Sort is needed.
        Node* pc=NULL;
        if(needsort)
        {
           if(pa==NULL)
           {
               pc=new Node();
               pc->value="Sort";
               pc->children[0]=q;
               pc->children[1]=pb;
               pc->childnum=2;
               sorttuples(pc,myschema_manager,mymem,intermediatenum);
           }
           else
           {
               pc=new Node();
               pc->value="Sort";
               pc->children[0]=pa;
               pc->children[1]=pb;
               pc->childnum=2;
               sorttuples(pc,myschema_manager,mymem,intermediatenum);
           }
        }
        Node* finalnode;
        if(pc!=NULL) finalnode=pc;
        else
        {
            if(pa!=NULL) finalnode=pa;
            else finalnode=q;
        }
        for(int i=0;i<finalnode->involvedtable.size();i++)
        {
            cout<<finalnode->involvedtable[i]<<"."<<finalnode->fieldname[i]<<"\t";
        }
        cout<<endl; 
        int tuplecount=0;
        if(finalnode->indisk)
        {
            for(int i=0;i<finalnode->relationlocation->getNumOfBlocks();i++)
            {
                Block* output=mymem.getBlock(1);
                finalnode->relationlocation->getBlock(i,1);
                for(int j=0;j<finalnode->relationlocation->getSchema().getTuplesPerBlock();j++)
                {
                    if(!(output->getTuple(j).isNull())) cout<<++tuplecount<<":  "<<output->getTuple(j)<<endl;
                }
                output->clear();
            }            
        }
        else
        {
            if(finalnode->memfront) position=2;
            else position=6;
            for(int i=0;i<4;i++)
            {
                Block* block_ptr=mymem.getBlock(i+position);
                for(int j=0;j<finalnode->relationlocation->getSchema().getTuplesPerBlock();j++)
                {
                    if(!(block_ptr->getTuple(j).isNull())) cout<<++tuplecount<<":  "<<block_ptr->getTuple(j)<<endl;
                }
            }
        }
        for(int i=0;i<intermediatenum;i++)
        {
            stringstream ss;
            ss<<i;
            Relation* tmprelation=myschema_manager.getRelation(ss.str());
            if(tmprelation->getNumOfBlocks()!=0) tmprelation->deleteBlocks(0);
            myschema_manager.deleteRelation(ss.str());
        }
    }
    
    void sorttuples(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,int& intermediatenum)
    {
        vector<int> sortfieldused;
        p->involvedtable=p->children[0]->involvedtable;
        p->fieldname=p->children[0]->fieldname;
        p->relationlocation=p->children[0]->relationlocation;
        string sorttable,sortattr;
        if(p->children[1]->childnum==3)
        {
            sorttable=p->children[1]->children[0]->children[0]->value;
            sortattr=p->children[1]->children[2]->children[0]->value;
        }
        else
        {
            sorttable=p->involvedtable[0];
            sortattr=p->children[1]->children[0]->children[0]->value;
        }
        int sortfieldnum;
        bool completematch=false;
        for(int i=0;i<p->involvedtable.size();i++)
        {
            sortfieldused.push_back(i);
            if(p->involvedtable[i]==sorttable && p->fieldname[i]==sortattr) 
            {
                sortfieldnum=i;
                completematch=true;
            }
        }
        if(!completematch)
        {
            for(int i=0;i<p->involvedtable.size();i++)
            {
                if(p->fieldname[i]==sortattr)
                {
                    sortfieldnum=i;
                    p->involvedtable[i]=sorttable;
                }
            }
        }
        int newtuplenum=0;
        //Relation is in mainmemory.
        if(p->children[0]->indisk==false)
        {
            Block* r[4];
            //Relation is in mainmory block 2-5.
            if(p->children[0]->memfront==true)
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+2);
                for(int m=0;m<4*p->relationlocation->getSchema().getTuplesPerBlock();m++)
                {
                    for(int i=0;i<4;i++)
                    {
                        for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(r[i]->getTuple(j).isNull()))
                            {
                                int k,l;
                                if(j==p->relationlocation->getSchema().getTuplesPerBlock()-1)
                                {
                                    k=i+1;
                                    l=0;
                                }
                                else
                                {
                                    k=i;
                                    l=j+1;
                                }
                                while(k<4 && r[k]->getTuple(l).isNull())
                                {
                                    l++;
                                    if(l==p->relationlocation->getSchema().getTuplesPerBlock())
                                    {
                                        k++;
                                        l=0;
                                    }
                                }
                                if(k<4)
                                {
                                    if(needswap(p,sortfieldnum,r[i]->getTuple(j),r[k]->getTuple(l),sortfieldused))
                                    {
                                        Tuple tmptuple=r[k]->getTuple(l);
                                        r[k]->nullTuple(l);
                                        r[k]->setTuple(l,r[i]->getTuple(j));
                                        r[i]->nullTuple(j);
                                        r[i]->setTuple(j,tmptuple);
                                    }
                                }
                            }
                        }
                    }
                }
                p->indisk=false;
                p->memfront=true;
            }
            //Relation is in mainmemory blocks 6-9.
            else
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+6);
                for(int m=0;m<4*p->relationlocation->getSchema().getTuplesPerBlock();m++)
                {
                    for(int i=0;i<4;i++)
                    {
                        for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(r[i]->getTuple(j).isNull()))
                            {
                                int k,l;
                                if(j==p->relationlocation->getSchema().getTuplesPerBlock()-1)
                                {
                                    k=i+1;
                                    l=0;
                                }
                                else
                                {
                                    k=i;
                                    l=j+1;
                                }
                                while(k<4 && r[k]->getTuple(l).isNull())
                                {
                                    l++;
                                    if(l==p->relationlocation->getSchema().getTuplesPerBlock())
                                    {
                                        k++;
                                        l=0;
                                    }
                                }
                                if(k<4)
                                {
                                    if(needswap(p,sortfieldnum,r[i]->getTuple(j),r[k]->getTuple(l),sortfieldused))
                                    {
                                        Tuple tmptuple=r[k]->getTuple(l);
                                        r[k]->nullTuple(l);
                                        r[k]->setTuple(l,r[i]->getTuple(j));
                                        r[i]->nullTuple(j);
                                        r[i]->setTuple(j,tmptuple);
                                    }
                                }
                            }
                        }
                    }
                }
                p->indisk=false;
                p->memfront=false;
            }
        }
        //Relation is in disk.
        else
        {
            //Relation has less than 4 blocks. The result can be kept in the mainmemory.
            if(p->relationlocation->getNumOfBlocks()<=4)
            {
                p->relationlocation->getBlocks(0,2,p->relationlocation->getNumOfBlocks());
                Block* r[4];
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+2);
                for(int m=0;m<4*p->relationlocation->getSchema().getTuplesPerBlock();m++)
                {
                    for(int i=0;i<4;i++)
                    {
                        for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(r[i]->getTuple(j).isNull()))
                            {
                                int k,l;
                                if(j==p->relationlocation->getSchema().getTuplesPerBlock()-1)
                                {
                                    k=i+1;
                                    l=0;
                                }
                                else
                                {
                                    k=i;
                                    l=j+1;
                                }
                                while(k<4 && r[k]->getTuple(l).isNull())
                                {
                                    l++;
                                    if(l==p->relationlocation->getSchema().getTuplesPerBlock())
                                    {
                                        k++;
                                        l=0;
                                    }
                                }
                                if(k<4)
                                {
                                    if(needswap(p,sortfieldnum,r[i]->getTuple(j),r[k]->getTuple(l),sortfieldused))
                                    {
                                        Tuple tmptuple=r[k]->getTuple(l);
                                        r[k]->nullTuple(l);
                                        r[k]->setTuple(l,r[i]->getTuple(j));
                                        r[i]->nullTuple(j);
                                        r[i]->setTuple(j,tmptuple);
                                    }
                                }
                            }
                        }
                    }
                }
                p->indisk=false;
                p->memfront=true;
            }
            else
            {
                //Relation has less than 8 blocks. One pass algorithm can be used but the result should be written to disk.
                if(p->relationlocation->getNumOfBlocks()<=8)
                {
                    p->relationlocation->getBlocks(0,2,p->relationlocation->getNumOfBlocks());
                    p->relationlocation->deleteBlocks(0);
                    Block* r[8];
                    for(int i=0;i<8;i++) r[i]=mymem.getBlock(i+2);
                    for(int m=0;m<8*p->relationlocation->getSchema().getTuplesPerBlock();m++)
                    {
                        for(int i=0;i<8;i++)
                        {
                            for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                            {
                                if(!(r[i]->getTuple(j).isNull()))
                                {
                                    int k,l;
                                    if(j==p->relationlocation->getSchema().getTuplesPerBlock()-1)
                                    {
                                        k=i+1;
                                        l=0;
                                    }
                                    else
                                    {
                                        k=i;
                                        l=j+1;
                                    }
                                    while(k<8 && r[k]->getTuple(l).isNull())
                                    {
                                        l++;
                                        if(l==p->relationlocation->getSchema().getTuplesPerBlock())
                                        {
                                            k++;
                                            l=0;
                                        }
                                    }
                                    if(k<8)
                                    {
                                        if(needswap(p,sortfieldnum,r[i]->getTuple(j),r[k]->getTuple(l),sortfieldused))
                                        {
                                            Tuple tmptuple=r[k]->getTuple(l);
                                            r[k]->nullTuple(l);
                                            r[k]->setTuple(l,r[i]->getTuple(j));
                                            r[i]->nullTuple(j);
                                            r[i]->setTuple(j,tmptuple);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    p->relationlocation->setBlocks(0,2,8);
                    p->indisk=true;
                    Block* cleanptr;
                    for(int i=0;i<10;i++)
                    {
                        cleanptr=mymem.getBlock(i);
                        cleanptr->clear();
                    }
                }
                //Relation has more than 8 blocks. Two pass algorithm should be used.                
                else
                {
                    int newtuplenum=0; 
                    sortboxes(p,myschema_manager,mymem,sortfieldnum,sortfieldused);
                    stringstream ss;
                    ss<<intermediatenum;
                    intermediatenum++;
                    Relation* tmprelation=myschema_manager.createRelation(ss.str(),p->relationlocation->getSchema());
                    int boxnum=p->relationlocation->getNumOfBlocks()/10;
                    if(p->relationlocation->getNumOfBlocks()%10!=0) boxnum++;
                    vector<int> eachboxblocknum;
                    vector<int> eachboxcount;
                    vector<int> eachblockcount;
                    vector<Block*> r;
                    //Therefore my algorithm can only work for relations that have less than 80 blocks.
                    for(int i=0;i<boxnum;i++)
                    {
                        r.push_back(mymem.getBlock(i+2));
                        eachboxcount.push_back(0);
                        eachblockcount.push_back(p->relationlocation->getSchema().getTuplesPerBlock());
                        eachboxblocknum.push_back(10+1);
                    }
                    if(p->relationlocation->getNumOfBlocks()%10!=0) eachboxblocknum[eachboxblocknum.size()-1]=p->relationlocation->getNumOfBlocks()%10+1;
                    bool notdoneyet=true;
                    while(notdoneyet)
                    {
                        int minitupleboxnum=0;
                        Tuple minituple=p->relationlocation->createTuple();
                        minituple.null();
                        for(int i=0;i<boxnum;i++)
                        {
                            if(eachboxcount[i]<eachboxblocknum[i] && eachblockcount[i]==p->relationlocation->getSchema().getTuplesPerBlock())
                            {
                                r[i]->clear();
                                if(eachboxcount[i]<eachboxblocknum[i]-1) p->relationlocation->getBlock(i*10+eachboxcount[i],i+2);
                                eachboxcount[i]++;
                                eachblockcount[i]=0;
                            }
                            while(eachboxcount[i]<eachboxblocknum[i] && r[i]->getTuple(eachblockcount[i]).isNull())
                            {
                                eachblockcount[i]++;
                                if(eachblockcount[i]==p->relationlocation->getSchema().getTuplesPerBlock())
                                {
                                    r[i]->clear();
                                    if(eachboxcount[i]<eachboxblocknum[i]-1) p->relationlocation->getBlock(i*10+eachboxcount[i],i+2);
                                    eachboxcount[i]++;
                                    eachblockcount[i]=0;                                    
                                }
                            }
                            if(!(r[i]->getTuple(eachblockcount[i]).isNull()))
                            {
                                if(minituple.isNull()) minituple=r[i]->getTuple(eachblockcount[i]);
                                else
                                {
                                    if(needswap(p,sortfieldnum,minituple,r[i]->getTuple(eachblockcount[i]),sortfieldused))
                                    {
                                        minituple=r[i]->getTuple(eachblockcount[i]);
                                        minitupleboxnum=i;
                                    }
                                }
                            }
                        }
                        eachblockcount[minitupleboxnum]++;
                        newtuplenum++;
                        if(newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock()!=0)
                        {
                            Block* resspace=mymem.getBlock(0);
                            resspace->appendTuple(minituple);
                        }
                        else
                        {
                            Block* resspace=mymem.getBlock(0);
                            resspace->appendTuple(minituple);
                            tmprelation->setBlock(tmprelation->getNumOfBlocks(),0);
                            resspace->clear();
                        }
                        notdoneyet=false;
                        for(int i=0;i<boxnum;i++)
                        {
                            if(eachboxcount[i]!=eachboxblocknum[i]) notdoneyet=true;
                        }
                    }
                    p->relationlocation=tmprelation;
                    p->indisk=true;
                    Block* cleanptr;
                    for(int i=0;i<10;i++)
                    {
                        cleanptr=mymem.getBlock(i);
                        cleanptr->clear();
                    }                   
                }
            }
        }
    }
    
    bool needswap(Node* p,int sortfieldnum,Tuple tuple1,Tuple tuple2,vector<int> sortfieldused)
    {
        if(p->relationlocation->getSchema().getFieldType(sortfieldused[sortfieldnum])==INT) 
        {
            if(tuple1.getField(sortfieldused[sortfieldnum]).integer==tuple2.getField(sortfieldused[sortfieldnum]).integer && sortfieldnum<sortfieldused.size()-1)
            {
                return needswap(p,sortfieldnum+1,tuple1,tuple2,sortfieldused);
            }
            else return tuple1.getField(sortfieldused[sortfieldnum]).integer>tuple2.getField(sortfieldused[sortfieldnum]).integer;
        }
        else
        {
            
            string string1=*(tuple1.getField(sortfieldused[sortfieldnum]).str);
            string string2=*(tuple2.getField(sortfieldused[sortfieldnum]).str);
            int i=0;
            while(i<min(string1.length(),string2.length()) && string1[i]==string2[i])
            {
                i++;
            }
            if(i==string1.length() || i==string2.length())
            {
                if(i==string2.length() && i==string1.length() && sortfieldnum<sortfieldused.size()-1)
                {
                    return needswap(p,sortfieldnum+1,tuple1,tuple2,sortfieldused);
                }
                if(i==string2.length()) return true;
                else return false;
            }
            else
            {
                return string1[i]>string2[i];
            }
        }
    }
    
    void eliminateduplicate(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,int& intermediatenum)
    {
        p->involvedtable=p->children[0]->involvedtable;
        p->fieldname=p->children[0]->fieldname;
        p->relationlocation=p->children[0]->relationlocation;
        //Relation is in the mainmemory.
        int newtuplenum=0;
        if(p->children[0]->indisk==false)
        {
            Block* r[4];
            //Relation is in mainmory block 2-5.
            if(p->children[0]->memfront==true)
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+2);
                for(int i=0;i<4;i++)
                {
                    Block* busyblock=mymem.getBlock(1);
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull())) busyblock->appendTuple(r[i]->getTuple(j));
                    }
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(busyblock->getTuple(j).isNull()))
                        {
                            int nomatch=true;
                            for(int k=0;k<4;k++)
                            {
                                for(int l=0;l<p->relationlocation->getSchema().getTuplesPerBlock();l++)
                                {
                                    if(!(r[k]->getTuple(l).isNull()))
                                    {
                                        if(twosametuples(p,busyblock->getTuple(j),r[k]->getTuple(l)))
                                        {
                                            nomatch=false;
                                            r[k]->nullTuple(l);
                                        }
                                    }
                                }
                            }
                            if(nomatch) busyblock->nullTuple(j);
                        }
                    }
                    Block* resspace=mymem.getBlock(i+6);
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(busyblock->getTuple(j).isNull())) resspace->appendTuple(busyblock->getTuple(j));
                    }
                    busyblock->clear();
                }
                p->indisk=false;
                p->memfront=false;
                for(int i=0;i<6;i++)
                {
                    Block* cleanptr=mymem.getBlock(i);
                    cleanptr->clear();
                }
            }
            //Relation is in mainmemory block 6-9.
            else
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+6);
                for(int i=0;i<4;i++)
                {
                    Block* busyblock=mymem.getBlock(1);
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull())) busyblock->appendTuple(r[i]->getTuple(j));
                    }
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(busyblock->getTuple(j).isNull()))
                        {
                            int nomatch=true;
                            for(int k=0;k<4;k++)
                            {
                                for(int l=0;l<p->relationlocation->getSchema().getTuplesPerBlock();l++)
                                {
                                    if(!(r[k]->getTuple(l).isNull()))
                                    {
                                        if(twosametuples(p,busyblock->getTuple(j),r[k]->getTuple(l)))
                                        {
                                            nomatch=false;
                                            r[k]->nullTuple(l);
                                        }
                                    }
                                }
                            }
                            if(nomatch) busyblock->nullTuple(j);
                        }
                    }
                    Block* resspace=mymem.getBlock(i+2);
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(busyblock->getTuple(j).isNull())) resspace->appendTuple(busyblock->getTuple(j));
                    }
                    busyblock->clear();
                }
                p->indisk=false;
                p->memfront=true;
                Block* cleanptr=mymem.getBlock(0);
                cleanptr->clear();
                cleanptr=mymem.getBlock(1);
                cleanptr->clear();
                for(int i=0;i<4;i++)
                {
                    cleanptr=mymem.getBlock(i+6);
                    cleanptr->clear();
                }
            }
        }
        //Relation is in disk.
        else
        {
            //Relation has less than 4 blocks. Duplicate eliminate result is allowed to be kept inside mainmemory.
            if(p->relationlocation->getNumOfBlocks()<=4)
            {
                Block* r[4];
                p->relationlocation->getBlocks(0,2,p->relationlocation->getNumOfBlocks());
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+2);
                for(int i=0;i<4;i++)
                {
                    Block* busyblock=mymem.getBlock(1);
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull())) busyblock->appendTuple(r[i]->getTuple(j));
                    }
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(busyblock->getTuple(j).isNull()))
                        {
                            int nomatch=true;
                            for(int k=0;k<4;k++)
                            {
                                for(int l=0;l<p->relationlocation->getSchema().getTuplesPerBlock();l++)
                                {
                                    if(!(r[k]->getTuple(l).isNull()))
                                    {
                                        if(twosametuples(p,busyblock->getTuple(j),r[k]->getTuple(l)))
                                        {
                                            nomatch=false;
                                            r[k]->nullTuple(l);
                                        }
                                    }
                                }
                            }
                            if(nomatch) busyblock->nullTuple(j);
                        }
                    }
                    Block* resspace=mymem.getBlock(i+6);
                    resspace->setTuples(busyblock->getTuples());
                    busyblock->clear();
                }
                p->indisk=false;
                p->memfront=false;
                for(int i=0;i<6;i++)
                {
                    Block* cleanptr=mymem.getBlock(i);
                    cleanptr->clear();
                }   
            }
            else
            {
                //Relation has less than 8 blocks. One pass algorithem is allowed but result should be written back to disk.
                if(p->relationlocation->getNumOfBlocks()<=8)
                {
                    Block* r[8];
                    p->relationlocation->getBlocks(0,2,p->relationlocation->getNumOfBlocks());
                    p->relationlocation->deleteBlocks(0);
                    for(int i=0;i<8;i++) r[i]=mymem.getBlock(i+2);
                    for(int i=0;i<8;i++)
                    {
                        Block* busyblock=mymem.getBlock(1);
                        for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(r[i]->getTuple(j).isNull())) busyblock->appendTuple(r[i]->getTuple(j));
                        }
                        for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(busyblock->getTuple(j).isNull()))
                            {
                                int nomatch=true;
                                for(int k=0;k<8;k++)
                                {
                                    for(int l=0;l<p->relationlocation->getSchema().getTuplesPerBlock();l++)
                                    {
                                        if(!(r[k]->getTuple(l).isNull()))
                                        {
                                            if(twosametuples(p,busyblock->getTuple(j),r[k]->getTuple(l)))
                                            {
                                                nomatch=false;
                                                r[k]->nullTuple(l);
                                            }
                                        }
                                    }
                                }
                                if(nomatch) busyblock->nullTuple(j);
                            }
                        }
                        p->relationlocation->setBlock(p->relationlocation->getNumOfBlocks(),1);
                        busyblock->clear();
                    }
                    p->indisk=true;
                    Block* cleanptr;
                    for(int i=0;i<10;i++)
                    {
                        cleanptr=mymem.getBlock(i);
                        cleanptr->clear();
                    }
                }
                //Relation is larger than 8 blocks. Two pass algorithem is needed.
                else
                {
                    vector<int> sortfieldused;
                    int newtuplenum=0;                    
                    for(int i=0;i<p->children[0]->relationlocation->getSchema().getNumOfFields();i++) sortfieldused.push_back(i);                    
                    sortboxes(p,myschema_manager,mymem,0,sortfieldused);
                    stringstream ss;
                    ss<<intermediatenum;
                    intermediatenum++;
                    Relation* tmprelation=myschema_manager.createRelation(ss.str(),p->relationlocation->getSchema());
                    int boxnum=p->relationlocation->getNumOfBlocks()/10;
                    if(p->relationlocation->getNumOfBlocks()%10!=0) boxnum++;
                    vector<int> eachboxblocknum;
                    vector<int> eachboxcount;
                    vector<int> eachblockcount;
                    vector<Block*> r;
                    //Therefore my algorithm can only work for relations that have less than 80 blocks.
                    for(int i=0;i<boxnum;i++)
                    {
                        r.push_back(mymem.getBlock(i+2));
                        eachboxcount.push_back(0);
                        eachblockcount.push_back(p->relationlocation->getSchema().getTuplesPerBlock());
                        eachboxblocknum.push_back(10+1);
                    }
                    if(p->relationlocation->getNumOfBlocks()%10!=0) eachboxblocknum[eachboxblocknum.size()-1]=p->relationlocation->getNumOfBlocks()%10+1;
                    bool notdoneyet=true;
                    while(notdoneyet)
                    {
                        Tuple minituple=p->relationlocation->createTuple();
                        minituple.null();
                        for(int i=0;i<boxnum;i++)
                        {
                            if(eachboxcount[i]<eachboxblocknum[i] && eachblockcount[i]==p->relationlocation->getSchema().getTuplesPerBlock())
                            {
                                r[i]->clear();
                                if(eachboxcount[i]<eachboxblocknum[i]-1) p->relationlocation->getBlock(i*10+eachboxcount[i],i+2);
                                eachboxcount[i]++;
                                eachblockcount[i]=0;
                            }
                            while(eachboxcount[i]<eachboxblocknum[i] && r[i]->getTuple(eachblockcount[i]).isNull())
                            {
                                eachblockcount[i]++;
                                if(eachblockcount[i]==p->relationlocation->getSchema().getTuplesPerBlock())
                                {
                                    r[i]->clear();
                                    if(eachboxcount[i]<eachboxblocknum[i]-1) p->relationlocation->getBlock(i*10+eachboxcount[i],i+2);
                                    eachboxcount[i]++;
                                    eachblockcount[i]=0;                                    
                                }
                            }
                            if(!(r[i]->getTuple(eachblockcount[i]).isNull()))
                            {
                                if(minituple.isNull()) minituple=r[i]->getTuple(eachblockcount[i]);
                                else
                                {
                                    if(needswap(p,0,minituple,r[i]->getTuple(eachblockcount[i]),sortfieldused)) minituple=r[i]->getTuple(eachblockcount[i]);
                                }
                            }
                        }
                        for(int i=0;i<boxnum;i++)
                        {
                            while(eachboxcount[i]<eachboxblocknum[i] && (r[i]->getTuple(eachblockcount[i]).isNull() || twosametuples(p,minituple,r[i]->getTuple(eachblockcount[i]))))
                            {
                                eachblockcount[i]++;
                                if(eachblockcount[i]==p->relationlocation->getSchema().getTuplesPerBlock())
                                {
                                    r[i]->clear();
                                    if(eachboxcount[i]<eachboxblocknum[i]-1) p->relationlocation->getBlock(i*10+eachboxcount[i],i+2);
                                    eachboxcount[i]++;
                                    eachblockcount[i]=0;                                    
                                }                                
                            }
                        }
                        newtuplenum++;
                        if(newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock()!=0)
                        {
                            Block* resspace=mymem.getBlock(0);
                            resspace->appendTuple(minituple);
                        }
                        else
                        {
                            Block* resspace=mymem.getBlock(0);
                            resspace->appendTuple(minituple);
                            tmprelation->setBlock(tmprelation->getNumOfBlocks(),0);
                            resspace->clear();
                        }
                        notdoneyet=false;
                        for(int i=0;i<boxnum;i++)
                        {
                            if(eachboxcount[i]!=eachboxblocknum[i]) notdoneyet=true;
                        }
                    }
                    p->relationlocation=tmprelation;
                    p->indisk=true;
                    Block* cleanptr;
                    for(int i=0;i<10;i++)
                    {
                        cleanptr=mymem.getBlock(i);
                        cleanptr->clear();
                    }
                }
            }
        }
    }
    
    void sortboxes(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,int sortfieldnum,vector<int> sortfieldused)
    {
        Block* cleanptr;
        for(int i=0;i<10;i++)
        {
            cleanptr=mymem.getBlock(i);
            cleanptr->clear();
        }
        int fullboxnum=p->relationlocation->getNumOfBlocks()/10;
        //Sort tuples in every box.
        for(int n=0;n<fullboxnum;n++)
        {
            p->relationlocation->getBlocks(n*10,0,10);
            Block* r[10];
            for(int i=0;i<10;i++) r[i]=mymem.getBlock(i);
            for(int m=0;m<10*p->relationlocation->getSchema().getTuplesPerBlock();m++)
            {
                for(int i=0;i<10;i++)
                {
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull()))
                        {
                            int k,l;
                            if(j==p->relationlocation->getSchema().getTuplesPerBlock()-1)
                            {
                                k=i+1;
                                l=0;
                            }
                            else
                            {
                                k=i;
                                l=j+1;
                            }
                            while(k<10 && r[k]->getTuple(l).isNull())
                            {
                                l++;
                                if(l==p->relationlocation->getSchema().getTuplesPerBlock())
                                {
                                    k++;
                                    l=0;
                                }
                            }
                            if(k<10)
                            {
                                if(needswap(p,sortfieldnum,r[i]->getTuple(j),r[k]->getTuple(l),sortfieldused))
                                {
                                    Tuple tmptuple=r[k]->getTuple(l);
                                    r[k]->nullTuple(l);
                                    r[k]->setTuple(l,r[i]->getTuple(j));
                                    r[i]->nullTuple(j);
                                    r[i]->setTuple(j,tmptuple);
                                }
                            }
                        }
                    }
                }
            }
            p->relationlocation->setBlocks(n*10,0,10);
            for(int i=0;i<10;i++)
            {
                cleanptr=mymem.getBlock(i);
                cleanptr->clear();
            }
        }
        int extrablock=p->relationlocation->getNumOfBlocks()%10;
        for(int i=0;i<10;i++)
        {
            cleanptr=mymem.getBlock(i);
            cleanptr->clear();
        }
        if(extrablock!=0)
        {
            p->relationlocation->getBlocks(fullboxnum*10,0,extrablock);
            vector<Block*> r;
            for(int i=0;i<extrablock;i++) r.push_back(mymem.getBlock(i));
            for(int m=0;m<extrablock*p->relationlocation->getSchema().getTuplesPerBlock();m++)
            {
                for(int i=0;i<extrablock;i++)
                {
                    for(int j=0;j<p->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull()))
                        {
                            int k,l;
                            if(j==p->relationlocation->getSchema().getTuplesPerBlock()-1)
                            {
                                k=i+1;
                                l=0;
                            }
                            else
                            {
                                k=i;
                                l=j+1;
                            }
                            while(k<extrablock && r[k]->getTuple(l).isNull())
                            {
                                l++;
                                if(l==p->relationlocation->getSchema().getTuplesPerBlock())
                                {
                                    k++;
                                    l=0;
                                }
                            }
                            if(k<extrablock)
                            {
                                if(needswap(p,sortfieldnum,r[i]->getTuple(j),r[k]->getTuple(l),sortfieldused))
                                {
                                    Tuple tmptuple=r[k]->getTuple(l);
                                    r[k]->nullTuple(l);
                                    r[k]->setTuple(l,r[i]->getTuple(j));
                                    r[i]->nullTuple(j);
                                    r[i]->setTuple(j,tmptuple);
                                }
                            }
                        }
                    }
                }
            }
            p->relationlocation->setBlocks(fullboxnum*10,0,extrablock);
            for(int i=0;i<10;i++)
            {
                cleanptr=mymem.getBlock(i);
                cleanptr->clear();
            }                        
        }        
    }
    
    bool twosametuples(Node* p,Tuple tuple1,Tuple tuple2)
    {
        bool sametuple=true;
        for(int i=0;i<p->involvedtable.size();i++)
        {
            if(p->relationlocation->getSchema().getFieldType(i)==INT)
            {
                if(tuple1.getField(i).integer!=tuple2.getField(i).integer) sametuple=false;
            }
            else
            {
                if(*(tuple1.getField(i).str)!=*(tuple2.getField(i).str)) sametuple=false;
            }
        }
        return sametuple;
    }
    
    void locaterelations(Node* p,SchemaManager& myschema_manager)
    {
        if(p->value=="table_in_sub" || p->value=="select_list" || p->value=="search_condition" || p->value=="boolean_term" || p->value=="boolean_factor") return;
        if(p->value!="projection" && p->value!="selection" && p->value!="cross_join" && p->value !="natural_join" && p->value!="theta_join")
        {
            p->relationlocation=myschema_manager.getRelation(p->value);
        }
        for(int i=0;i<p->childnum;i++) locaterelations(p->children[i],myschema_manager);
    }
    
    void execuateselectquery(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,Node*& prenode,int& intermediatenum,bool multitable)
    {
        for(int i=0;i<p->childnum;i++) execuateselectquery(p->children[i],myschema_manager,mymem,prenode,intermediatenum,multitable);
        if(p->value=="natural_join") 
        {
            needtowritedisk(prenode,p,myschema_manager,mymem);
            execuatenatural(p,myschema_manager,mymem,intermediatenum,0);
        }
        if(p->value=="theta_join")
        {
            needtowritedisk(prenode,p,myschema_manager,mymem);
            execuatenatural(p,myschema_manager,mymem,intermediatenum,1);
        }
        if(p->value=="projection")
        {
            execuateprojection(p,myschema_manager,mymem,intermediatenum);
        }
        if(p->value=="selection")
        {
            execuateselection(p,myschema_manager,mymem,intermediatenum,multitable);
        }
        if(p->value=="cross_join")
        {
            needtowritedisk(prenode,p,myschema_manager,mymem);
            execuatenatural(p,myschema_manager,mymem,intermediatenum,2);
        }
        prenode=p;
    }
    
    void execuateselection(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,int& intermediatenum,bool multitable)
    {
        vector<string> field_names;
        vector<enum FIELD_TYPE> field_types;
        for(int ia=0;ia<p->involvedtable.size();ia++)
        {
            stringstream ss;
            ss<<ia;
            field_names.push_back(ss.str());
            field_types.push_back(myschema_manager.getSchema(p->involvedtable[ia]).getFieldType(p->fieldname[ia]));
        }
        Schema newschema(field_names,field_types);
        stringstream ss;
        ss<<intermediatenum;
        p->relationlocation=myschema_manager.createRelation(ss.str(),newschema);
        intermediatenum++;
        Relation* relation1=p->children[0]->relationlocation;
        //Relation is in the mainmemory.
        int newtuplenum=0;
        if(p->children[0]->indisk==false)
        {
            Block* r[4];
            //Relation is in mainmory block 2-5.
            if(p->children[0]->memfront==true)
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+2);
                for(int i=0;i<4;i++)
                {
                    for(int j=0;j<relation1->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull()))
                        {
                            if(satisfycondition(r[i]->getTuple(j),p->children[1],multitable,p,myschema_manager))
                            {
                                newtuplenum++;
                                Tuple newtuple=p->relationlocation->createTuple();
                                constructtupleafterselction(r[i]->getTuple(j),p,newtuple);
                                Block* resspace=mymem.getBlock((newtuplenum-1)/p->relationlocation->getSchema().getTuplesPerBlock()+6);
                                resspace->appendTuple(newtuple);
                            }
                        }
                    }
                }
                p->indisk=false;
                p->memfront=false;
                for(int i=0;i<6;i++)
                {
                    Block* cleanptr=mymem.getBlock(i);
                    cleanptr->clear();
                }
            }
            //Relation is in mainmemory block 6-9.
            else
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+6);
                for(int i=0;i<4;i++)
                {
                    for(int j=0;j<relation1->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull()))
                        {
                            if(satisfycondition(r[i]->getTuple(j),p->children[1],multitable,p,myschema_manager))
                            {
                                newtuplenum++;
                                Tuple newtuple=p->relationlocation->createTuple();
                                constructtupleafterselction(r[i]->getTuple(j),p,newtuple);
                                Block* resspace=mymem.getBlock((newtuplenum-1)/p->relationlocation->getSchema().getTuplesPerBlock()+2);
                                resspace->appendTuple(newtuple);
                            }
                        }
                    }
                }
                p->indisk=false;
                p->memfront=true;
                Block* cleanptr=mymem.getBlock(0);
                cleanptr->clear();
                cleanptr=mymem.getBlock(1);
                cleanptr->clear();
                for(int i=0;i<4;i++)
                {
                    cleanptr=mymem.getBlock(i+6);
                    cleanptr->clear();
                }
            
            }
        }
        //Relation is in disk.
        else
        {
            //Relation has less than 4 blocks. Selection result is allowed to be kept inside mainmemory.
            if(relation1->getNumOfBlocks()<=4)
            {
                Block* r[4];
                relation1->getBlocks(0,2,relation1->getNumOfBlocks());
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(i+2);
                for(int i=0;i<4;i++)
                {
                    for(int j=0;j<relation1->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull()))
                        {
                            if(satisfycondition(r[i]->getTuple(j),p->children[1],multitable,p,myschema_manager))
                            {
                                newtuplenum++;
                                Tuple newtuple=p->relationlocation->createTuple();
                                constructtupleafterselction(r[i]->getTuple(j),p,newtuple);
                                Block* resspace=mymem.getBlock((newtuplenum-1)/p->relationlocation->getSchema().getTuplesPerBlock()+6);
                                resspace->appendTuple(newtuple);
                            }
                        }
                    }
                }
                p->indisk=false;
                p->memfront=false;
                for(int i=0;i<6;i++)
                {
                    Block* cleanptr=mymem.getBlock(i);
                    cleanptr->clear();
                }                   
            }
            else
            {
                //Relation has more than 4 blocks. Result should be written back to disk.
                Block* busyblock=mymem.getBlock(1);
                Block* resspace=mymem.getBlock(0);
                busyblock->clear();
                resspace->clear();
                for(int i=0;i<relation1->getNumOfBlocks();i++)
                {
                    relation1->getBlock(i,1);
                    for(int j=0;j<relation1->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(busyblock->getTuple(j).isNull()))
                        {
                            if(satisfycondition(busyblock->getTuple(j),p->children[1],multitable,p,myschema_manager))
                            {
                                newtuplenum++;
                                Tuple newtuple=p->relationlocation->createTuple();
                                constructtupleafterselction(busyblock->getTuple(j),p,newtuple);
                                if((newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                                {
                                    resspace->appendTuple(newtuple);
                                }
                                else
                                {
                                    resspace->appendTuple(newtuple);
                                    p->relationlocation->setBlock(p->relationlocation->getNumOfBlocks(),0);
                                    resspace->clear();
                                }
                            }
                        }
                    }
                    busyblock->clear();
                }
                if((newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                {
                    p->relationlocation->setBlock(p->relationlocation->getNumOfBlocks(),0);
                }
                p->indisk=true;
                Block* cleanptr;
                for(int i=0;i<10;i++)
                {
                    cleanptr=mymem.getBlock(i);
                    cleanptr->clear();
                }
            }
        }
    }
    
    void constructtupleafterselction(Tuple tuple,Node* p,Tuple& newtuple)
    {
        for(int i=0;i<p->involvedtable.size();i++)
        {
            for(int j=0;j<p->children[0]->involvedtable.size();j++)
            {
                if(p->involvedtable[i]==p->children[0]->involvedtable[j] && p->fieldname[i]==p->children[0]->fieldname[j])
                {
                    if(tuple.getSchema().getFieldType(j)==INT) newtuple.setField(i,tuple.getField(j).integer);
                    else newtuple.setField(i,*(tuple.getField(j).str));
                }
            }
        }
    }
    
    void execuateprojection(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,int& intermediatenum)
    {
        if(p->children[1]->children[0]->value=="*")
        {
            p->indisk=p->children[0]->indisk;
            p->relationlocation=p->children[0]->relationlocation;
            p->memfront=p->children[0]->memfront;
            return;
        }
        vector<string> field_names;
        vector<enum FIELD_TYPE> field_types;
        for(int ia=0;ia<p->involvedtable.size();ia++)
        {
            stringstream ss;
            ss<<ia;
            field_names.push_back(ss.str());
            field_types.push_back(myschema_manager.getSchema(p->involvedtable[ia]).getFieldType(p->fieldname[ia]));
        }
        Schema newschema(field_names,field_types);
        stringstream ss;
        ss<<intermediatenum;
        p->relationlocation=myschema_manager.createRelation(ss.str(),newschema);
        intermediatenum++;
        Relation* relation1=p->children[0]->relationlocation;
        //Relation is in the mainmemory.
        int newtuplenum=0;
        if(p->children[0]->indisk==false)
        {
            Block* r[4];
            //Relation is in the mainmemory blocks 2-5.
            if(p->children[0]->memfront==true)
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(2+i);
                for(int i=0;i<4;i++)
                {
                    for(int j=0;j<relation1->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull()))
                        {
                            Tuple newtuple=p->relationlocation->createTuple();
                            getprojection(p,r[i]->getTuple(j),newtuple);
                            newtuplenum++;
                            Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+6);
                            resspace->appendTuple(newtuple);
                        }
                    }
                }
                p->indisk=false;
                p->memfront=false;
                for(int i=0;i<6;i++)
                {
                    Block* cleanptr=mymem.getBlock(i);
                    cleanptr->clear();
                }
            }
            //Relation is in the mainmemory blocks 6-9.
            else
            {
                for(int i=0;i<4;i++) r[i]=mymem.getBlock(6+i);
                for(int i=0;i<4;i++)
                {
                    for(int j=0;j<relation1->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(r[i]->getTuple(j).isNull()))
                        {
                            Tuple newtuple=p->relationlocation->createTuple();
                            getprojection(p,r[i]->getTuple(j),newtuple);
                            newtuplenum++;
                            Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+2);
                            resspace->appendTuple(newtuple);                
                        }
                    }
                }
                p->indisk=false;
                p->memfront=true;
                Block* cleanptr=mymem.getBlock(0);
                cleanptr->clear();
                cleanptr=mymem.getBlock(1);
                cleanptr->clear();
                for(int i=0;i<4;i++)
                {
                    cleanptr=mymem.getBlock(i+6);
                    cleanptr->clear();
                }                
            }
        }
        //Relation is in the disk
        else
        {
            Block* ncleanptr;
            for(int i=0;i<10;i++)
            {
                ncleanptr=mymem.getBlock(i);
                ncleanptr->clear();
            }
            Block* busyblock;
            busyblock=mymem.getBlock(1);
            newtuplenum=0;
            for(int i=0;i<relation1->getNumOfBlocks();i++)
            {
                relation1->getBlock(i,1);
                for(int j=0;j<relation1->getSchema().getTuplesPerBlock();j++)
                {
                    if(!(busyblock->getTuple(j).isNull()))
                    {
                        Tuple newtuple=p->relationlocation->createTuple();
                        getprojection(p,busyblock->getTuple(j),newtuple);
                        newtuplenum++;
                        if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                        {
                            Block* resspace=mymem.getBlock((newtuplenum-1)/p->relationlocation->getSchema().getTuplesPerBlock()+2);
                            resspace->appendTuple(newtuple);
                        }
                        if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                        {
                            p->relationlocation->setBlocks(0,2,4);
                            Block* resspace=mymem.getBlock(0);
                            resspace->appendTuple(newtuple);
                            if(p->relationlocation->getSchema().getTuplesPerBlock()==1)
                            {
                                p->relationlocation->setBlock(p->relationlocation->getNumOfBlocks(),0);
                                resspace->clear();
                            }
                        }
                        if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                        {
                            if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                            {
                                Block* resspace=mymem.getBlock(0);
                                resspace->appendTuple(newtuple);
                            }
                            else
                            {
                                Block* resspace=mymem.getBlock(0);
                                resspace->appendTuple(newtuple);
                                p->relationlocation->setBlock(p->relationlocation->getNumOfBlocks(),0);
                                resspace->clear();
                            }
                        }
                    }
                }
            }
            if(newtuplenum>4*p->relationlocation->getSchema().getTuplesPerBlock() && (newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
            {
                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
            }
            Block* cleanptr=mymem.getBlock(0);
            cleanptr->clear();
            cleanptr=mymem.getBlock(1);
            cleanptr->clear();
            if(newtuplenum<=4*p->relationlocation->getSchema().getTuplesPerBlock())
            {
                p->indisk=false;
                p->memfront=true;
                for(int ib=6;ib<10;ib++)
                {
                    cleanptr=mymem.getBlock(ib);
                    cleanptr->clear();
                }
            }
            else
            {
                p->indisk=true;
                for(int ib=2;ib<10;ib++)
                {
                    cleanptr=mymem.getBlock(ib);
                    cleanptr->clear();
                }
            }
        }
    }
    
    void getprojection(Node* p,Tuple tuple1,Tuple& newtuple)
    {
        for(int i=0;i<p->involvedtable.size();i++)
        {
            bool completematch=false;
            for(int j=0;j<p->children[0]->involvedtable.size();j++)
            {
                if(p->involvedtable[i]==p->children[0]->involvedtable[j] && p->fieldname[i]==p->children[0]->fieldname[j])
                {
                    if(newtuple.getSchema().getFieldType(i)==INT) newtuple.setField(i,tuple1.getField(j).integer);
                    else newtuple.setField(i,*(tuple1.getField(j).str));
                    completematch=true;
                }
            }
            if(!completematch)
            {
                for(int j=0;j<p->children[0]->involvedtable.size();j++)
                {
                    if(p->fieldname[i]==p->children[0]->fieldname[j])
                    {
                        if(newtuple.getSchema().getFieldType(i)==INT) newtuple.setField(i,tuple1.getField(j).integer);
                        else newtuple.setField(i,*(tuple1.getField(j).str));
                        completematch=true;
                    }
                }                
            }
        }
    }
    
    void execuatenatural(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,int& intermediatenum,int crossthetanatural)
    {
        vector<string> field_names;
        vector<enum FIELD_TYPE> field_types;
        for(int ia=0;ia<p->involvedtable.size();ia++)
        {
            stringstream ss;
            ss<<ia;
            field_names.push_back(ss.str());
            field_types.push_back(myschema_manager.getSchema(p->involvedtable[ia]).getFieldType(p->fieldname[ia]));
        }
        Schema newschema(field_names,field_types);
        stringstream ss;
        ss<<intermediatenum;
        p->relationlocation=myschema_manager.createRelation(ss.str(),newschema);
        intermediatenum++;
        Relation* relation1;
        Relation* relation2;
        Node* tmpnodefortheta=new Node();
        for(int i=0;i<4;i++) tmpnodefortheta->children[i]=p->children[i];
        tmpnodefortheta->childnum=4;
        SelectStatProcessor assistn;
        assistn.estimatecross(tmpnodefortheta);
        field_names.clear();
        field_types.clear();
        for(int ia=0;ia<tmpnodefortheta->involvedtable.size();ia++)
        {
            stringstream ss;
            ss<<ia;
            field_names.push_back(ss.str());
            field_types.push_back(myschema_manager.getSchema(tmpnodefortheta->involvedtable[ia]).getFieldType(tmpnodefortheta->fieldname[ia]));
        }
        Schema nnewschema(field_names,field_types);
        stringstream nss;
        nss<<intermediatenum;
        tmpnodefortheta->relationlocation=myschema_manager.createRelation(nss.str(),nnewschema);
        intermediatenum++;
        //One of the relations is in the mainmemory. One pass algorithm should definitely be used.
        if(p->children[0]->indisk==false || p->children[2]->indisk==false)
        {
            //Relation1 is in the mainmemory.
            if(p->children[0]->indisk==false)
            {
                relation1=p->children[0]->relationlocation;
                relation2=p->children[2]->relationlocation;
                Block* r1[4];  
                //Relation1 is in mainmemory blocks 2-5.
                if(p->children[0]->memfront==true)
                {
                    int newtuplenum=0;
                    for(int i=0;i<4;i++) r1[i]=mymem.getBlock(2+i);
                    for(int i=0;i<relation2->getNumOfBlocks();i++)
                    {
                        relation2->getBlock(i,1);
                        Block* busyblock=mymem.getBlock(1);
                        for(int j=0;j<relation2->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(busyblock->getTuple(j).isNull()))
                            {
                                for(int l=0;l<4;l++)
                                {
                                    for(int k=0;k<relation1->getSchema().getTuplesPerBlock();k++)
                                    {
                                        if(!(r1[l]->getTuple(k).isNull()))
                                        {
                                            if(crossthetanatural==2 || (crossthetanatural==0 && satisfynaturaljoin(p,busyblock->getTuple(j),r1[l]->getTuple(k),2,0)))
                                            {
                                                newtuplenum++;
                                                Tuple newtuple=p->relationlocation->createTuple();
                                                constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,2,0,crossthetanatural);
                                                if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                {
                                                    Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+6);
                                                    resspace->appendTuple(newtuple);
                                                }
                                                if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    p->relationlocation->setBlocks(0,6,4);
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                    if(newtuple.getTuplesPerBlock()==1)
                                                    {
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                                if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                    }
                                                    else
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                            }
                                            else
                                            {
                                                //If theta join.
                                                if(crossthetanatural==1)
                                                {
                                                    Tuple testtuple=tmpnodefortheta->relationlocation->createTuple();
                                                    constructnewtuple(tmpnodefortheta,busyblock->getTuple(j),r1[l]->getTuple(k),testtuple,2,0,2);
                                                    bool satisfytheta=true;
                                                    for(int im=4;im<p->childnum;im++)
                                                    {
                                                        if(!satisfycondition(testtuple,p->children[im],true,tmpnodefortheta,myschema_manager)) satisfytheta=false;
                                                    }
                                                    if(satisfytheta)
                                                    {
                                                        newtuplenum++;
                                                        Tuple newtuple=p->relationlocation->createTuple();
                                                        constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,2,0,crossthetanatural);
                                                        if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                        {
                                                            Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+6);
                                                            resspace->appendTuple(newtuple);
                                                        }
                                                        if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            p->relationlocation->setBlocks(0,6,4);
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                            if(newtuple.getTuplesPerBlock()==1)
                                                            {
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }
                                                        if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                            }
                                                            else
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }                                                        
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if(newtuplenum>4*p->relationlocation->getSchema().getTuplesPerBlock() && (newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                    {
                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                    }
                    Block* cleanptr=mymem.getBlock(0);
                    cleanptr->clear();
                    cleanptr=mymem.getBlock(1);
                    cleanptr->clear();
                    if(newtuplenum<=4*p->relationlocation->getSchema().getTuplesPerBlock())
                    {
                        p->indisk=false;
                        p->memfront=false;
                        for(int ib=2;ib<6;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                    else
                    {
                        p->indisk=true;
                        for(int ib=2;ib<10;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                }
                //Relation1 is in mainmemory block 6-9;
                else
                {
                    int newtuplenum=0;
                    for(int i=0;i<4;i++) r1[i]=mymem.getBlock(6+i);
                    for(int i=0;i<relation2->getNumOfBlocks();i++)
                    {
                        relation2->getBlock(i,1);
                        Block* busyblock=mymem.getBlock(1);
                        for(int j=0;j<relation2->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(busyblock->getTuple(j).isNull()))
                            {
                                for(int l=0;l<4;l++)
                                {
                                    for(int k=0;k<relation1->getSchema().getTuplesPerBlock();k++)
                                    {
                                        if(!(r1[l]->getTuple(k).isNull()))
                                        {
                                            if(crossthetanatural==2 || (crossthetanatural==0 && satisfynaturaljoin(p,busyblock->getTuple(j),r1[l]->getTuple(k),2,0)))
                                            {
                                                newtuplenum++;
                                                Tuple newtuple=p->relationlocation->createTuple();
                                                constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,2,0,crossthetanatural);
                                                if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                {
                                                    Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+2);
                                                    resspace->appendTuple(newtuple);
                                                }
                                                if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    p->relationlocation->setBlocks(0,2,4);
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                    if(newtuple.getTuplesPerBlock()==1)
                                                    {
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                                if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                    }
                                                    else
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                            }
                                            else
                                            {
                                                //If theta join.
                                                if(crossthetanatural==1)
                                                {
                                                    Tuple testtuple=tmpnodefortheta->relationlocation->createTuple();
                                                    constructnewtuple(tmpnodefortheta,busyblock->getTuple(j),r1[l]->getTuple(k),testtuple,2,0,2);
                                                    bool satisfytheta=true;
                                                    for(int im=4;im<p->childnum;im++)
                                                    {
                                                        if(!satisfycondition(testtuple,p->children[im],true,tmpnodefortheta,myschema_manager)) satisfytheta=false;
                                                    }
                                                    if(satisfytheta)
                                                    {
                                                        newtuplenum++;
                                                        Tuple newtuple=p->relationlocation->createTuple();
                                                        constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,2,0,crossthetanatural);
                                                        if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                        {
                                                            Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+2);
                                                            resspace->appendTuple(newtuple);
                                                        }
                                                        if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            p->relationlocation->setBlocks(0,6,4);
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                            if(newtuple.getTuplesPerBlock()==1)
                                                            {
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }
                                                        if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                            }
                                                            else
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }                                                        
                                                    }                                                    
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if(newtuplenum>4*p->relationlocation->getSchema().getTuplesPerBlock() && (newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                    {
                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                    }
                    Block* cleanptr=mymem.getBlock(0);
                    cleanptr->clear();
                    cleanptr=mymem.getBlock(1);
                    cleanptr->clear();
                    if(newtuplenum<=4*p->relationlocation->getSchema().getTuplesPerBlock())
                    {
                        p->indisk=false;
                        p->memfront=true;
                        for(int ib=6;ib<10;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                    else
                    {
                        p->indisk=true;
                        for(int ib=2;ib<10;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                }
            }
            //Relation2 is in mainmemory.
            if(p->children[2]->indisk==false)
            {

                relation2=p->children[0]->relationlocation;
                relation1=p->children[2]->relationlocation;
                Block* r1[4];
                //Relation2 is in mainmemory block 2-5.                
                if(p->children[2]->memfront==true)
                {
                    int newtuplenum=0;
                    for(int i=0;i<4;i++) r1[i]=mymem.getBlock(2+i);
                    for(int i=0;i<relation2->getNumOfBlocks();i++)
                    {
                        relation2->getBlock(i,1);
                        Block* busyblock=mymem.getBlock(1);
                        for(int j=0;j<relation2->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(busyblock->getTuple(j).isNull()))
                            {
                                for(int l=0;l<4;l++)
                                {
                                    for(int k=0;k<relation1->getSchema().getTuplesPerBlock();k++)
                                    {
                                        if(!(r1[l]->getTuple(k).isNull()))
                                        {
                                            if(crossthetanatural==2 || (crossthetanatural==0 && satisfynaturaljoin(p,busyblock->getTuple(j),r1[l]->getTuple(k),0,2)))
                                            {
                                                newtuplenum++;
                                                Tuple newtuple=p->relationlocation->createTuple();
                                                constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,0,2,crossthetanatural);
                                                if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                {
                                                    Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+6);
                                                    resspace->appendTuple(newtuple);
                                                }
                                                if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    p->relationlocation->setBlocks(0,6,4);
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                    if(newtuple.getTuplesPerBlock()==1)
                                                    {
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                                if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                    }
                                                    else
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                            }
                                            else
                                            {
                                                //If theta join.
                                                if(crossthetanatural==1)
                                                {
                                                    Tuple testtuple=tmpnodefortheta->relationlocation->createTuple();
                                                    constructnewtuple(tmpnodefortheta,busyblock->getTuple(j),r1[l]->getTuple(k),testtuple,0,2,2);
                                                    bool satisfytheta=true;
                                                    for(int im=4;im<p->childnum;im++)
                                                    {
                                                        if(!satisfycondition(testtuple,p->children[im],true,tmpnodefortheta,myschema_manager)) satisfytheta=false;
                                                    }
                                                    if(satisfytheta)
                                                    {
                                                        newtuplenum++;
                                                        Tuple newtuple=p->relationlocation->createTuple();
                                                        constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,0,2,crossthetanatural);
                                                        if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                        {
                                                            Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+6);
                                                            resspace->appendTuple(newtuple);
                                                        }
                                                        if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            p->relationlocation->setBlocks(0,6,4);
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                            if(newtuple.getTuplesPerBlock()==1)
                                                            {
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }
                                                        if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                            }
                                                            else
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }                                                        
                                                    } 
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if(newtuplenum>4*p->relationlocation->getSchema().getTuplesPerBlock() && (newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                    {
                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                    }
                    Block* cleanptr=mymem.getBlock(0);
                    cleanptr->clear();
                    cleanptr=mymem.getBlock(1);
                    cleanptr->clear();
                    if(newtuplenum<=4*p->relationlocation->getSchema().getTuplesPerBlock())
                    {
                        p->indisk=false;
                        p->memfront=false;
                        for(int ib=2;ib<6;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                    else
                    {
                        p->indisk=true;
                        for(int ib=2;ib<10;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                }
                //Relation2 is in mainmemory blocks 6-9;
                else
                {
                    int newtuplenum=0;
                    for(int i=0;i<4;i++) r1[i]=mymem.getBlock(6+i);
                    for(int i=0;i<relation2->getNumOfBlocks();i++)
                    {
                        relation2->getBlock(i,1);
                        Block* busyblock=mymem.getBlock(1);
                        for(int j=0;j<relation2->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(busyblock->getTuple(j).isNull()))
                            {
                                for(int l=0;l<4;l++)
                                {
                                    for(int k=0;k<relation1->getSchema().getTuplesPerBlock();k++)
                                    {
                                        if(!(r1[l]->getTuple(k).isNull()))
                                        {
                                            if(crossthetanatural==2 || (crossthetanatural==0 && satisfynaturaljoin(p,busyblock->getTuple(j),r1[l]->getTuple(k),0,2)))
                                            {
                                                newtuplenum++;
                                                Tuple newtuple=p->relationlocation->createTuple();
                                                constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,0,2,crossthetanatural);
                                                if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                {
                                                    Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+2);
                                                    resspace->appendTuple(newtuple);
                                                }
                                                if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    p->relationlocation->setBlocks(0,2,4);
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                    if(newtuple.getTuplesPerBlock()==1)
                                                    {
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                                if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                {
                                                    if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                    }
                                                    else
                                                    {
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                        resspace->clear();
                                                    }
                                                }
                                            }
                                            else
                                            {
                                                //If theta join.
                                                if(crossthetanatural==1)
                                                {
                                                    Tuple testtuple=tmpnodefortheta->relationlocation->createTuple();
                                                    constructnewtuple(tmpnodefortheta,busyblock->getTuple(j),r1[l]->getTuple(k),testtuple,0,2,2);
                                                    bool satisfytheta=true;
                                                    for(int im=4;im<p->childnum;im++)
                                                    {
                                                        if(!satisfycondition(testtuple,p->children[im],true,tmpnodefortheta,myschema_manager)) satisfytheta=false;
                                                    }
                                                    if(satisfytheta)
                                                    {
                                                        newtuplenum++;
                                                        Tuple newtuple=p->relationlocation->createTuple();
                                                        constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,0,2,crossthetanatural);
                                                        if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                        {
                                                            Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+2);
                                                            resspace->appendTuple(newtuple);
                                                        }
                                                        if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            p->relationlocation->setBlocks(0,6,4);
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                            if(newtuple.getTuplesPerBlock()==1)
                                                            {
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }
                                                        if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                        {
                                                            if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                            }
                                                            else
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                                p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                resspace->clear();
                                                            }
                                                        }                                                        
                                                    }
                                                } 
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if(newtuplenum>4*p->relationlocation->getSchema().getTuplesPerBlock() && (newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                    {
                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                    }
                    Block* cleanptr=mymem.getBlock(0);
                    cleanptr->clear();
                    cleanptr=mymem.getBlock(1);
                    cleanptr->clear();
                    if(newtuplenum<=4*p->relationlocation->getSchema().getTuplesPerBlock())
                    {
                        p->indisk=false;
                        p->memfront=true;
                        for(int ib=6;ib<10;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                    else
                    {
                        p->indisk=true;
                        for(int ib=2;ib<10;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }
                    }
                }
            }
        }
        //Two relations are all in disk.
        else
        {
            int size1=p->children[0]->relationlocation->getNumOfBlocks();
            int size2=p->children[2]->relationlocation->getNumOfBlocks();
            //One relation is smaller than 4 blocks. One pass algorithm should be used and the result is possible to be stored inside the mainmemory.
            if(min(size1,size2)<=4)
            {
                int relationone;
                int relationtwo;
                if(size1<=size2) 
                {
                    relation1=p->children[0]->relationlocation;
                    relation2=p->children[2]->relationlocation;
                    relation1->getBlocks(0,2,size1);
                    relationone=2;
                    relationtwo=0;
                }
                else 
                {
                    relation1=p->children[2]->relationlocation;
                    relation2=p->children[0]->relationlocation;
                    relation1->getBlocks(0,2,size2);
                    relationone=0;
                    relationtwo=2;
                }
                Block* r1[4]; 
                int newtuplenum=0;
                for(int i=0;i<4;i++) r1[i]=mymem.getBlock(2+i);
                for(int i=0;i<relation2->getNumOfBlocks();i++)
                {
                    relation2->getBlock(i,1);
                    Block* busyblock=mymem.getBlock(1);
                    for(int j=0;j<relation2->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(busyblock->getTuple(j).isNull()))
                        {
                            for(int l=0;l<4;l++)
                            {
                                for(int k=0;k<relation1->getSchema().getTuplesPerBlock();k++)
                                {
                                    if(!(r1[l]->getTuple(k).isNull()))
                                    {
                                        if(crossthetanatural==2 || (crossthetanatural==0 && satisfynaturaljoin(p,busyblock->getTuple(j),r1[l]->getTuple(k),relationone,relationtwo)))
                                        {
                                            newtuplenum++;
                                            Tuple newtuple=p->relationlocation->createTuple();
                                            constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,relationone,relationtwo,crossthetanatural);
                                            if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                            {
                                                Block* resspace=mymem.getBlock(((newtuplenum-1)/newtuple.getTuplesPerBlock())+6);
                                                resspace->appendTuple(newtuple);
                                            }
                                            if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                            {
                                                p->relationlocation->setBlocks(0,6,4);
                                                Block* resspace=mymem.getBlock(0);
                                                resspace->appendTuple(newtuple);
                                                if(newtuple.getTuplesPerBlock()==1)
                                                {
                                                    p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                    resspace->clear();
                                                }
                                            }
                                            if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                            {
                                                if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                {
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                }
                                                else
                                                {
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                    p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                    resspace->clear();
                                                }
                                            }
                                        }
                                        else
                                        {
                                            //If theta join.
                                            if(crossthetanatural==1)
                                            {
                                                Tuple testtuple=tmpnodefortheta->relationlocation->createTuple();
                                                constructnewtuple(tmpnodefortheta,busyblock->getTuple(j),r1[l]->getTuple(k),testtuple,relationone,relationtwo,2);
                                                bool satisfytheta=true;
                                                for(int im=4;im<p->childnum;im++)
                                                {
                                                    if(!satisfycondition(testtuple,p->children[im],true,tmpnodefortheta,myschema_manager)) satisfytheta=false;
                                                }
                                                if(satisfytheta)
                                                {
                                                    newtuplenum++;
                                                    Tuple newtuple=p->relationlocation->createTuple();
                                                    constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,relationone,relationtwo,crossthetanatural);
                                                    if(newtuplenum<=4*newtuple.getTuplesPerBlock())
                                                    {
                                                        Block* resspace=mymem.getBlock((newtuplenum-1)/newtuple.getTuplesPerBlock()+6);
                                                        resspace->appendTuple(newtuple);
                                                    }
                                                    if(newtuplenum==4*newtuple.getTuplesPerBlock()+1)
                                                    {
                                                        p->relationlocation->setBlocks(0,6,4);
                                                        Block* resspace=mymem.getBlock(0);
                                                        resspace->appendTuple(newtuple);
                                                        if(newtuple.getTuplesPerBlock()==1)
                                                        {
                                                            p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                            resspace->clear();
                                                        }
                                                    }
                                                    if(newtuplenum>4*newtuple.getTuplesPerBlock()+1)
                                                    {
                                                        if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                        {
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                        }
                                                        else
                                                        {
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                            p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                            resspace->clear();
                                                        }
                                                    }                                                        
                                                }                                                
                                            } 
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if(newtuplenum>4*p->relationlocation->getSchema().getTuplesPerBlock() && (newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                {
                    p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                }
                Block* cleanptr=mymem.getBlock(0);
                cleanptr->clear();
                cleanptr=mymem.getBlock(1);
                cleanptr->clear();
                if(newtuplenum<=4*p->relationlocation->getSchema().getTuplesPerBlock())
                {
                    p->indisk=false;
                    p->memfront=false;
                    for(int ib=2;ib<6;ib++)
                    {
                        cleanptr=mymem.getBlock(ib);
                        cleanptr->clear();
                    }
                }
                else
                {
                    p->indisk=true;
                    for(int ib=2;ib<10;ib++)
                    {
                        cleanptr=mymem.getBlock(ib);
                        cleanptr->clear();
                    }
                }
               
            }
            else
            {
                //One relation can be hold by mainmemory. One pass algorithm should be used but the result should be written to disk.
                if(min(size1,size2)<=8)
                {
                    int relationone;
                    int relationtwo;
                    if(size1<=size2) 
                    {
                        relation1=p->children[0]->relationlocation;
                        relation2=p->children[2]->relationlocation;
                        relation1->getBlocks(0,2,size1);
                        relationone=2;
                        relationtwo=0;
                    }
                    else 
                    {
                        relation1=p->children[2]->relationlocation;
                        relation2=p->children[0]->relationlocation;
                        relation1->getBlocks(0,2,size2);
                        relationone=0;
                        relationtwo=2;
                    }
                    Block* r1[8]; 
                    int newtuplenum=0;
                    for(int i=0;i<8;i++) r1[i]=mymem.getBlock(2+i);
                    for(int i=0;i<relation2->getNumOfBlocks();i++)
                    {
                        relation2->getBlock(i,1);
                        Block* busyblock=mymem.getBlock(1);
                        for(int j=0;j<relation2->getSchema().getTuplesPerBlock();j++)
                        {
                            if(!(busyblock->getTuple(j).isNull()))
                            {
                                for(int l=0;l<8;l++)
                                {
                                    for(int k=0;k<relation1->getSchema().getTuplesPerBlock();k++)
                                    {
                                        if(!(r1[l]->getTuple(k).isNull()))
                                        {
                                            if(crossthetanatural==2 || (crossthetanatural==0 && satisfynaturaljoin(p,busyblock->getTuple(j),r1[l]->getTuple(k),relationone,relationtwo)))
                                            {
                                                newtuplenum++;
                                                Tuple newtuple=p->relationlocation->createTuple();
                                                constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,relationone,relationtwo,crossthetanatural);
                                                if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                {
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                }
                                                else
                                                {
                                                    Block* resspace=mymem.getBlock(0);
                                                    resspace->appendTuple(newtuple);
                                                    p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                    resspace->clear();
                                                }
                                            }
                                            else
                                            {
                                                //If theta join.
                                                if(crossthetanatural==1)
                                                {
                                                    Tuple testtuple=tmpnodefortheta->relationlocation->createTuple();
                                                    constructnewtuple(tmpnodefortheta,busyblock->getTuple(j),r1[l]->getTuple(k),testtuple,relationone,relationtwo,2);
                                                    bool satisfytheta=true;
                                                    for(int im=4;im<p->childnum;im++)
                                                    {
                                                        if(!satisfycondition(testtuple,p->children[im],true,tmpnodefortheta,myschema_manager)) satisfytheta=false;
                                                    }
                                                    if(satisfytheta)
                                                    {
                                                        newtuplenum++;
                                                        Tuple newtuple=p->relationlocation->createTuple();
                                                        constructnewtuple(p,busyblock->getTuple(j),r1[l]->getTuple(k),newtuple,relationone,relationtwo,crossthetanatural);
                                                        if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                        {
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                        }
                                                        else
                                                        {
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                            p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                            resspace->clear();
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    if((newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                    {
                        p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                    }
                    Block* cleanptr=mymem.getBlock(0);
                    cleanptr->clear();
                    cleanptr=mymem.getBlock(1);
                    cleanptr->clear();
                    p->indisk=true;
                    for(int ib=2;ib<10;ib++)
                    {
                        cleanptr=mymem.getBlock(ib);
                        cleanptr->clear();
                    }
                }
                //Two relations are all too large to be held in mainmemory. Two pass algorithm should be used. The result is possible to be stored inside the mainmemory.
                else
                {
                    //Nested algorithm for cross and theta join.
                    if(crossthetanatural!=0)
                    {
                        int relationone;
                        int relationtwo;
                        if(size1<=size2) 
                        {
                            relation1=p->children[0]->relationlocation;
                            relation2=p->children[2]->relationlocation;
                            relationone=0;
                            relationtwo=2;
                        }
                        else 
                        {
                            relation1=p->children[2]->relationlocation;
                            relation2=p->children[0]->relationlocation;
                            relationone=2;
                            relationtwo=0;
                        }
                        Block* r1[8]; 
                        int newtuplenum=0;
                        for(int i=0;i<8;i++) r1[i]=mymem.getBlock(2+i);
                        for(int i=0;i<(relation1->getNumOfBlocks()-1)/8+1;i++)
                        {
                            int usefulblocknum;                           
                            if((relation1->getNumOfBlocks()-8*i)>8) usefulblocknum=8;
                            else usefulblocknum=relation1->getNumOfBlocks()-8*i;
                            relation1->getBlocks(i*8,2,usefulblocknum);
                            for(int l=0;l<relation2->getNumOfBlocks();l++)
                            {
                                Block* busyblock=mymem.getBlock(1);
                                relation2->getBlock(l,1);
                                for(int j=0;j<usefulblocknum;j++)
                                {
                                    for(int k=0;k<relation1->getSchema().getTuplesPerBlock();k++)
                                    {
                                        if(!(r1[j]->getTuple(k).isNull()))
                                        {
                                            for(int m=0;m<relation2->getSchema().getTuplesPerBlock();m++)
                                            {
                                                if(!(busyblock->getTuple(m).isNull()))
                                                {
                                                    if(crossthetanatural==2 || (crossthetanatural==0 && satisfynaturaljoin(p,busyblock->getTuple(j),r1[l]->getTuple(k),relationone,relationtwo)))
                                                    {
                                                        newtuplenum++;
                                                        Tuple newtuple=p->relationlocation->createTuple();
                                                        constructnewtuple(p,r1[j]->getTuple(k),busyblock->getTuple(m),newtuple,relationone,relationtwo,crossthetanatural);
                                                        if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                        {
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                        }
                                                        else
                                                        {
                                                            Block* resspace=mymem.getBlock(0);
                                                            resspace->appendTuple(newtuple);
                                                            p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                            resspace->clear();
                                                        }
                                                    }
                                                    else
                                                    {
                                                        //If theta join.
                                                        if(crossthetanatural==1)
                                                        {
                                                            Tuple testtuple=tmpnodefortheta->relationlocation->createTuple();
                                                            constructnewtuple(tmpnodefortheta,r1[j]->getTuple(k),busyblock->getTuple(m),testtuple,relationone,relationtwo,2);
                                                            bool satisfytheta=true;
                                                            for(int im=4;im<p->childnum;im++)
                                                            {
                                                                if(!satisfycondition(testtuple,p->children[im],true,tmpnodefortheta,myschema_manager)) satisfytheta=false;
                                                            }
                                                            if(satisfytheta)
                                                            {
                                                                newtuplenum++;
                                                                Tuple newtuple=p->relationlocation->createTuple();
                                                                constructnewtuple(p,r1[j]->getTuple(k),busyblock->getTuple(m),newtuple,relationone,relationtwo,crossthetanatural);
                                                                if((newtuplenum%newtuple.getTuplesPerBlock())!=0)
                                                                {
                                                                    Block* resspace=mymem.getBlock(0);
                                                                    resspace->appendTuple(newtuple);
                                                                }
                                                                else
                                                                {
                                                                    Block* resspace=mymem.getBlock(0);
                                                                    resspace->appendTuple(newtuple);
                                                                    p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                                                                    resspace->clear();
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                busyblock->clear();
                            }
                            for(int l=0;l<8;l++) r1[l]->clear();
                        }
                        if((newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                        {
                            p->relationlocation->setBlocks(p->relationlocation->getNumOfBlocks(),0,1);
                        }
                        Block* cleanptr=mymem.getBlock(0);
                        cleanptr->clear();
                        cleanptr=mymem.getBlock(1);
                        cleanptr->clear();
                        p->indisk=true;
                        for(int ib=2;ib<10;ib++)
                        {
                            cleanptr=mymem.getBlock(ib);
                            cleanptr->clear();
                        }                        
                    }
                    //Two pass sort_based algorithm for natural join.
                    else
                    {
                        int newtuplenum=0;
                        vector<int> sharedattrone;
                        vector<int> sharedattrtwo;
                        getsharedattrs(p,sharedattrone,sharedattrtwo);
                        Relation* relation1=p->children[0]->relationlocation;
                        Relation* relation2=p->children[2]->relationlocation;
                        sortboxes(p->children[0],myschema_manager,mymem,0,sharedattrone);
                        sortboxes(p->children[2],myschema_manager,mymem,0,sharedattrtwo);
                        int boxnum1=relation1->getNumOfBlocks()/10;
                        if(relation1->getNumOfBlocks()%10!=0) boxnum1++;
                        int boxnum2=relation2->getNumOfBlocks()/10;
                        if(relation2->getNumOfBlocks()%10!=0) boxnum2++;
                        vector<int> eachboxblocknum1,eachboxblocknum2;
                        vector<int> eachboxcount1,eachboxcount2;
                        vector<int> eachblockcount1,eachblockcount2;
                        vector<Block*> r1,r2;
                        int in;
                        for(in=0;in<boxnum1;in++)
                        {
                            r1.push_back(mymem.getBlock(in+2));
                            eachboxcount1.push_back(0);
                            eachblockcount1.push_back(relation1->getSchema().getTuplesPerBlock());
                            eachboxblocknum1.push_back(10+1);
                        }
                        if(relation1->getNumOfBlocks()%10!=0) eachboxblocknum1[eachboxblocknum1.size()-1]=relation1->getNumOfBlocks()%10+1;
                        for(in=0;in<boxnum2;in++)
                        {
                            r2.push_back(mymem.getBlock(in+6));
                            eachboxcount2.push_back(0);
                            eachblockcount2.push_back(relation2->getSchema().getTuplesPerBlock());
                            eachboxblocknum2.push_back(10+1);
                        }
                        if(relation2->getNumOfBlocks()%10!=0) eachboxblocknum2[eachboxblocknum2.size()-1]=relation2->getNumOfBlocks()%10+1;
                        bool notdoneyet=true;
                        int miniboxnum1,miniboxnum2;
                        while(notdoneyet)
                        {
                            //Find out the minimum tuples of the two relations by sorting according to common attributes.
                            Tuple minituple1=relation1->createTuple();
                            minituple1.null();
                            for(int i=0;i<boxnum1;i++)
                            {
                                if(eachboxcount1[i]<eachboxblocknum1[i] && eachblockcount1[i]==relation1->getSchema().getTuplesPerBlock())
                                {
                                    r1[i]->clear();
                                    if(eachboxcount1[i]<eachboxblocknum1[i]-1) relation1->getBlock(i*10+eachboxcount1[i],i+2);
                                    eachboxcount1[i]++;
                                    eachblockcount1[i]=0;
                                }
                                while(eachboxcount1[i]<eachboxblocknum1[i] && r1[i]->getTuple(eachblockcount1[i]).isNull())
                                {
                                    eachblockcount1[i]++;
                                    if(eachblockcount1[i]==relation1->getSchema().getTuplesPerBlock())
                                    {
                                        r1[i]->clear();
                                        if(eachboxcount1[i]<eachboxblocknum1[i]-1) relation1->getBlock(i*10+eachboxcount1[i],i+2);
                                        eachboxcount1[i]++;
                                        eachblockcount1[i]=0;                                    
                                    }
                                }
                                if(!(r1[i]->getTuple(eachblockcount1[i]).isNull()))
                                {
                                    if(minituple1.isNull()) minituple1=r1[i]->getTuple(eachblockcount1[i]);
                                    else
                                    {
                                        if(needswap(p->children[0],0,minituple1,r1[i]->getTuple(eachblockcount1[i]),sharedattrone))
                                        {
                                            minituple1=r1[i]->getTuple(eachblockcount1[i]);
                                            miniboxnum1=i;
                                        }
                                    }
                                }
                            }
                            Tuple minituple2=relation2->createTuple();
                            minituple2.null();
                            for(int i=0;i<boxnum2;i++)
                            {
                                if(eachboxcount2[i]<eachboxblocknum2[i] && eachblockcount2[i]==relation2->getSchema().getTuplesPerBlock())
                                {
                                    r2[i]->clear();
                                    if(eachboxcount2[i]<eachboxblocknum2[i]-1) relation2->getBlock(i*10+eachboxcount2[i],i+6);
                                    eachboxcount2[i]++;
                                    eachblockcount2[i]=0;
                                }
                                while(eachboxcount2[i]<eachboxblocknum2[i] && r2[i]->getTuple(eachblockcount2[i]).isNull())
                                {
                                    eachblockcount2[i]++;
                                    if(eachblockcount2[i]==p->relationlocation->getSchema().getTuplesPerBlock())
                                    {
                                        r2[i]->clear();
                                        if(eachboxcount2[i]<eachboxblocknum2[i]-1) relation2->getBlock(i*10+eachboxcount2[i],i+6);
                                        eachboxcount2[i]++;
                                        eachblockcount2[i]=0;     
                                    }
                                }
                                if(!(r2[i]->getTuple(eachblockcount2[i]).isNull()))
                                {
                                    if(minituple2.isNull()) minituple2=r2[i]->getTuple(eachblockcount2[i]);
                                    else
                                    {
                                        if(needswap(p->children[2],0,minituple2,r2[i]->getTuple(eachblockcount2[i]),sharedattrtwo))
                                        {
                                            minituple2=r2[i]->getTuple(eachblockcount2[i]);
                                            miniboxnum2=i;
                                        }
                                    }
                                }                                
                            }
                            if(!minituple1.isNull() && !minituple2.isNull())
                            {
                                //The outer loop iterate on all the tuples which can be join with the minituple2.
                                if(satisfynaturaljoin(p,minituple1,minituple2,0,2))
                                {
                                    vector<int> recordboxcount2,recordblockcount2;
                                    for(int i=0;i<boxnum1;i++)
                                    {
                                        while(eachboxcount1[i]<eachboxblocknum1[i] && (r1[i]->getTuple(eachblockcount1[i]).isNull() || satisfynaturaljoin(p,r1[i]->getTuple(eachblockcount1[i]),minituple2,0,2)))
                                        {
                                            if(!(r1[i]->getTuple(eachblockcount1[i]).isNull()))
                                            {
                                                recordblockcount2.clear();
                                                recordboxcount2.clear();
                                                recordblockcount2=eachblockcount2;
                                                recordboxcount2=eachboxcount2;
                                                for(int j=0;j<boxnum2;j++)
                                                {
                                                    while(recordboxcount2[j]<eachboxblocknum2[j] && (r2[j]->getTuple(recordblockcount2[j]).isNull() || satisfynaturaljoin(p,r2[j]->getTuple(recordblockcount2[j]),minituple1,2,0)))
                                                    {
                                                        if(!(r2[j]->getTuple(recordblockcount2[j]).isNull()))
                                                        {
                                                            Tuple newtuple=p->relationlocation->createTuple();
                                                            constructnewtuple(p,r1[i]->getTuple(eachblockcount1[i]),r2[j]->getTuple(recordblockcount2[j]),newtuple,0,2,0);
                                                            newtuplenum++;
                                                            if((newtuplenum%p->relationlocation->getSchema().getTuplesPerBlock())!=0)
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                            }
                                                            else
                                                            {
                                                                Block* resspace=mymem.getBlock(0);
                                                                resspace->appendTuple(newtuple);
                                                                p->relationlocation->setBlock(p->relationlocation->getNumOfBlocks(),0);
                                                                resspace->clear();
                                                            }
                                                        }
                                                        recordblockcount2[j]++;
                                                        if(recordblockcount2[j]==relation2->getSchema().getTuplesPerBlock())
                                                        {
                                                            r2[j]->clear();
                                                            if(recordboxcount2[j]<eachboxblocknum2[j]-1) relation2->getBlock(j*10+recordboxcount2[j],j+6);
                                                            recordboxcount2[j]++;
                                                            recordblockcount2[j]=0;
                                                        }
                                                    }
                                                }
                                                for(int j=0;j<boxnum2;j++)
                                                {
                                                    r2[j]->clear();
                                                    if(eachboxcount2[j]-1<eachboxblocknum2[j]-1) relation2->getBlock(j*10+eachboxcount2[j]-1,j+6);
                                                }
                                            }
                                            eachblockcount1[i]++;
                                            if(eachblockcount1[i]==relation1->getSchema().getTuplesPerBlock())
                                            {
                                                r1[i]->clear();
                                                if(eachboxcount1[i]<eachboxblocknum1[i]-1) relation1->getBlock(i*10+eachboxcount1[i],i+2);
                                                eachboxcount1[i]++;
                                                eachblockcount1[i]=0;                                    
                                            }                                
                                        }
                                    }
                                    eachboxcount2.clear();
                                    eachblockcount2.clear();
                                    eachboxcount2=recordboxcount2;
                                    eachblockcount2=recordblockcount2;
                                    for(int j=0;j<boxnum2;j++)
                                    {
                                        r2[j]->clear();
                                        if(eachboxcount2[j]-1<eachboxblocknum2[j]-1) relation2->getBlock(j*10+eachboxcount2[j]-1,j+6);
                                    }
                                }
                                else
                                {
                                    if(larger(minituple1,minituple2,sharedattrone,sharedattrtwo))
                                    {
                                        for(int i=0;i<boxnum2;i++)
                                        {
                                            while(eachboxcount2[i]<eachboxblocknum2[i] && (r2[i]->getTuple(eachblockcount2[i]).isNull() || !(larger(r2[i]->getTuple(eachblockcount2[i]),minituple2,sharedattrtwo,sharedattrtwo))))
                                            {
                                                eachboxcount2[i]++;
                                                if(eachboxcount2[i]==relation2->getSchema().getTuplesPerBlock())
                                                {
                                                    r2[i]->clear();
                                                    if(eachboxcount2[i]<eachboxblocknum2[i]-1) relation2->getBlock(i*10+eachboxcount2[i],i+6);
                                                    eachboxcount2[i]++;
                                                    eachblockcount2[i]=0;
                                                }
                                            }
                                        }
                                    }
                                    else 
                                    {
                                        for(int i=0;i<boxnum1;i++)
                                        {
                                            while(eachboxcount1[i]<eachboxblocknum1[i] && (r1[i]->getTuple(eachblockcount1[i]).isNull() || !(larger(r1[i]->getTuple(eachblockcount1[i]),minituple1,sharedattrone,sharedattrone))))
                                            {
                                                eachboxcount1[i]++;
                                                if(eachboxcount1[i]==relation1->getSchema().getTuplesPerBlock())
                                                {
                                                    r1[i]->clear();
                                                    if(eachboxcount1[i]<eachboxblocknum1[i]-1) relation1->getBlock(i*10+eachboxcount2[i],i+2);
                                                    eachboxcount1[i]++;
                                                    eachblockcount1[i]=0;
                                                }
                                            }
                                        }                                        
                                    }
                                }
                                bool notdoneyet1=false;
                                for(int i=0;i<boxnum1;i++)
                                {
                                    if(eachboxcount1[i]<eachboxblocknum1[i]) notdoneyet1=true;
                                }
                                bool notdoneyet2=false;
                                for(int i=0;i<boxnum2;i++)
                                {
                                    if(eachboxcount2[i]<eachboxblocknum2[i]) notdoneyet2=true;
                                }
                                if(!notdoneyet1 || !notdoneyet2) notdoneyet=false;
                            }
                            else
                            {
                                notdoneyet=false;
                            }
                        }
                        if((newtuplenum%p->relationlocation->getNumOfBlocks())!=0)
                        {
                            Block* resspace=mymem.getBlock(0);
                            p->relationlocation->setBlock(p->relationlocation->getNumOfBlocks(),0);
                        }
                        p->indisk=true;
                        Block* cleanptr;
                        for(int i=0;i<10;i++)
                        {
                            cleanptr=mymem.getBlock(i);
                            cleanptr->clear();
                        }
                    }
                }
            }
        }
    }
    
    //If two tuples for natural join can't be join, tell which one is the larger tuple.
    bool larger(Tuple tuple1,Tuple tuple2,vector<int> sharedattrone,vector<int> sharedattrtwo)
    {
        for(int i=0;i<sharedattrone.size();i++)
        {
            if(tuple1.getSchema().getFieldType(sharedattrone[i])==INT)
            {
                if(tuple1.getField(sharedattrone[i]).integer>tuple2.getField(sharedattrtwo[i]).integer) return true;
            }
            else
            {
                string string1=*(tuple1.getField(sharedattrone[i]).str);
                string string2=*(tuple2.getField(sharedattrtwo[i]).str);
                int j=0;
                while(i<min(string1.length(),string2.length()) && string1[j]==string2[j])
                {
                    j++;
                } 
                if(i==string2.length() && string1.length()!=string2.length()) return true;
                else
                {
                    if(string1[i]>string2[j]) return true;
                }
            }
        }
        return false;
    }
    
    void getsharedattrs(Node* p,vector<int>& sharedattrone,vector<int>& sharedattrtwo)
    {
        for(int i=0;i<p->children[0]->involvedtable.size();i++)
        {
            for(int j=0;j<p->children[2]->involvedtable.size();j++)
            {
                if(p->children[0]->fieldname[i]==p->children[2]->fieldname[j])
                {
                    sharedattrone.push_back(i);
                    sharedattrtwo.push_back(j);
                }
            }
        }
    }    
    
    void constructnewtuple(Node* p,Tuple tuple1,Tuple tuple2,Tuple& newtuple,int relation1,int relation2,int crossthetanatural)
    {
        for(int i=0;i<p->involvedtable.size();i++)
        {
            for(int j=0;j<p->children[relation1]->involvedtable.size();j++)
            {
                if(p->fieldname[i]==p->children[relation1]->fieldname[j] && (p->involvedtable[i]==p->children[relation1]->involvedtable[j] || crossthetanatural==0))
                {
                    if(newtuple.getSchema().getFieldType(i)==INT) newtuple.setField(i,tuple1.getField(j).integer);
                    else newtuple.setField(i,*(tuple1.getField(j).str));
                }
            }
            for(int j=0;j<p->children[relation2]->involvedtable.size();j++)
            {
                if(p->fieldname[i]==p->children[relation2]->fieldname[j] && (p->involvedtable[i]==p->children[relation2]->involvedtable[j] || crossthetanatural==0)) 
                {
                    if(newtuple.getSchema().getFieldType(i)==INT) newtuple.setField(i,tuple2.getField(j).integer);
                    else newtuple.setField(i,*(tuple2.getField(j).str));
                }
            }            
        }
    }
    
    bool satisfynaturaljoin(Node* p,Tuple tuple1,Tuple tuple2,int relation1,int relation2)
    {
        bool satisfy=true;
        for(int i=0;i<p->children[relation1]->involvedtable.size();i++)
        {
            for(int j=0;j<p->children[relation2]->involvedtable.size();j++)
            {
                if(p->children[relation1]->fieldname[i]==p->children[relation2]->fieldname[j])
                {
                    if(tuple1.getSchema().getFieldType(i)==INT)
                    {
                        if(tuple1.getField(i).integer!=tuple2.getField(j).integer) satisfy=false;
                    }
                    else
                    {
                        if(*(tuple1.getField(i).str)!=*(tuple2.getField(j).str)) satisfy=false;                        
                    }
                }
            }
        }
        return satisfy;
    }
    
    void needtowritedisk(Node* prenode,Node* p,SchemaManager& myschema_manager,MainMemory& mymem)
    {
        if(prenode->indisk==false)
        {
            if(p->children[0]!=p && p->children[2]!=p)
            {
                if(prenode->memfront==true)
                {
                    prenode->relationlocation->deleteBlocks(0);
                    prenode->relationlocation->setBlocks(0,2,4);
                    prenode->indisk=true;
                }
                else
                {
                    prenode->relationlocation->deleteBlocks(0);
                    prenode->relationlocation->setBlocks(0,6,4);
                    prenode->indisk=true;
                }
            }
        }
    }
    
    void selectstatement(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,bool withininsert, Relation* insertinto,int& newtuplenum)
    {
        for(int i=0;i<10;i++)
        {
            Block* cleanallblock=mymem.getBlock(i);
            cleanallblock->clear();
        }        
        bool hascondition=false;
        int fromposition=0;
        Node* prenode;
        int intermediatenum=0;
        for(int i=0;i<p->childnum;i++)
        {
            if(p->children[i]->value=="WHERE") hascondition=true;
            if(p->children[i]->value=="FROM") fromposition=i;
        }
        Node *pa=new Node();
        pa->value=p->children[fromposition+1]->children[0]->children[0]->value;
        pa->childnum=0;
        pa->indisk=true;
        pa->relationlocation=myschema_manager.getRelation(pa->value);
        vector<string> field_names=pa->relationlocation->getSchema().getFieldNames();
        for(int i=0;i<field_names.size();i++)
        {
            pa->involvedtable.push_back(pa->value);
            pa->fieldname.push_back(field_names[i]);
            pa->valuecount.push_back(0);
        }
        Node* pb=NULL;
        if(hascondition)
        {
            pb=new Node();
            pb->value="selection";
            pb->children[0]=pa;
            pb->children[1]=p->children[fromposition+3];
            pb->childnum=2;
            pb->involvedtable=pa->involvedtable;
            pb->fieldname=pa->fieldname;
        }
        Node* pc=new Node();
        pc->value="projection";
        if(pb!=NULL) pc->children[0]=pb;
        else pc->children[0]=pa;
        pc->children[1]=p->children[fromposition-1];
        pc->childnum=2;
        SelectStatProcessor assist;
        assist.estimateprojection(pc);
        Node* pd=NULL;
        if(p->children[1]->value=="DISTINCT")
        {
            pd=new Node();
            pd->value="duplicate_elimination";
            pd->children[0]=pc;
            pd->childnum=0;
        }
        bool needsort=false;
        int orderposition=0;
        Node* pe=NULL;
        for(int i=0;i<p->childnum;i++)
        {
            if(p->children[i]->value=="ORDER") 
            {
                pe=new Node();
                needsort=true;
                pe=p->children[i+2];
            }
        }
        Node* pf=NULL;
        if(needsort)
        {
            pf=new Node();
            pf->value="Sort";
            if(pd==NULL) pf->children[0]=pc;
            else pf->children[0]=pd;
            pf->children[1]=pe;
            pf->childnum=2;
        }
        execuateselectquery(pc,myschema_manager,mymem,prenode,intermediatenum,false);
        if(pd!=NULL) eliminateduplicate(pd,myschema_manager,mymem,intermediatenum);
        if(pf!=NULL) sorttuples(pf,myschema_manager,mymem,intermediatenum);
        Node* finalnode;
        if(pf!=NULL) finalnode=pf;
        else
        {
            if(pd!=NULL) finalnode=pd;
            else finalnode=pc;
        }
        if(!withininsert)
        {
            for(int i=0;i<finalnode->involvedtable.size();i++)
            {
                cout<<finalnode->fieldname[i]<<"\t";
            }
        }
        cout<<endl;
        int tuplecount=0;
        if(!(finalnode->indisk))
        {
            if(finalnode->memfront)
            {
                for(int i=0;i<4;i++)
                {
                    Block* output=mymem.getBlock(2+i);
                    for(int j=0;j<finalnode->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(output->getTuple(j).isNull())) 
                        {
                            if(withininsert)
                            {
                                Tuple newtuple=insertinto->createTuple();
                                for(int k=0;k<newtuple.getSchema().getNumOfFields();k++)
                                {
                                    if(newtuple.getSchema().getFieldType(k)==INT) newtuple.setField(k,output->getTuple(j).getField(k).integer);
                                    else newtuple.setField(k,*(output->getTuple(j).getField(k).str));
                                }                                
                                newtuplenum++;
                                Block* resspace=mymem.getBlock(0);
                                if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0)
                                {
                                    resspace->appendTuple(newtuple);
                                }
                                else
                                {
                                    resspace->appendTuple(newtuple);
                                    insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                                    resspace->clear();
                                }
                            }
                            else
                            {
                                tuplecount++;
                                cout<<tuplecount<<":  "<<output->getTuple(j)<<endl;
                            }
                        }
                    }
                }
                if(withininsert)
                {
                    if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0) 
                    {
                        insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                        Block* cleanptr=mymem.getBlock(0);
                        cleanptr->clear();
                    }
                }
            }
            else
            {
                for(int i=0;i<4;i++)
                {
                    Block* output=mymem.getBlock(6+i);
                    for(int j=0;j<finalnode->relationlocation->getSchema().getTuplesPerBlock();j++)
                    {
                        if(!(output->getTuple(j).isNull()))
                        {
                            if(withininsert)
                            {
                                Tuple newtuple=insertinto->createTuple();
                                for(int k=0;k<newtuple.getSchema().getNumOfFields();k++)
                                {
                                    if(newtuple.getSchema().getFieldType(k)==INT) newtuple.setField(k,output->getTuple(j).getField(k).integer);
                                    else newtuple.setField(k,*(output->getTuple(j).getField(k).str));
                                }
                                newtuplenum++;
                                Block* resspace=mymem.getBlock(0);
                                if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0)
                                {
                                    resspace->appendTuple(newtuple);
                                }
                                else
                                {
                                    resspace->appendTuple(newtuple);
                                    insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                                    resspace->clear();
                                }
                            }
                            else
                            {
                                tuplecount++;
                                cout<<tuplecount<<":  "<<output->getTuple(j)<<endl;
                            }
                        }
                    }
                }
                if(withininsert)
                {
                    if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0) 
                    {
                        insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                        Block* cleanptr=mymem.getBlock(0);
                        cleanptr->clear();
                    }
                }                
            }
        }
        else
        {
            for(int i=0;i<finalnode->relationlocation->getNumOfBlocks();i++)
            {
                Block* output=mymem.getBlock(1);
                finalnode->relationlocation->getBlock(i,1);
                for(int j=0;j<finalnode->relationlocation->getSchema().getTuplesPerBlock();j++)
                {
                    if(!(output->getTuple(j).isNull()))
                    {
                        if(withininsert)
                        {
                            Tuple newtuple=insertinto->createTuple();
                            for(int k=0;k<newtuple.getSchema().getNumOfFields();k++)
                            {
                                if(newtuple.getSchema().getFieldType(k)==INT) newtuple.setField(k,output->getTuple(j).getField(k).integer);
                                else newtuple.setField(k,*(output->getTuple(j).getField(k).str));
                            }                            
                            newtuplenum++;
                            Block* resspace=mymem.getBlock(0);
                            if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0)
                            {
                                resspace->appendTuple(newtuple);
                            }
                            else
                            {
                                resspace->appendTuple(newtuple);
                                insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                                resspace->clear();
                            }
                        }
                        else
                        {
                            tuplecount++;
                            cout<<tuplecount<<":  "<<output->getTuple(j)<<endl;
                        }                        
                    }
                }
                output->clear();
            }
            if(withininsert)
            {
                if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0) 
                {
                    insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                    Block* cleanptr=mymem.getBlock(0);
                    cleanptr->clear();
                }
            }            
        }
        for(int i=0;i<intermediatenum;i++)
        {
            stringstream ss;
            ss<<i;
            Relation* tmprelation=myschema_manager.getRelation(ss.str());
            if(tmprelation->getNumOfBlocks()!=0) tmprelation->deleteBlocks(0);
            myschema_manager.deleteRelation(ss.str());            
        }
        /*int newtuplenum=0;
        Block* cleanptr=mymem.getBlock(0);
        cleanptr->clear();
        bool hascondition=false;
        int fromposition=0;
        for(int i=0;i<p->childnum;i++)
        {
            if(p->children[i]->value=="WHERE") hascondition=true;
            if(p->children[i]->value=="FROM") fromposition=i;
            
        }
        if(hascondition)
        {
            Relation* q=myschema_manager.getRelation(p->children[fromposition+1]->children[0]->children[0]->value);
            vector<string> column=projectfield(p->children[fromposition-1]);                      
            if(!withininsert)
            {
                if(column[0]=="*")
                {
                    vector<string> field_names=q->getSchema().getFieldNames();
                    for(int i=0;i<field_names.size();i++) cout<<field_names[i]<<"\t";
                    cout<<endl;
                }
                else
                {
                    for(int k=0;k<column.size();k++) cout<<column[k]<<"\t";
                    cout<<endl;                
                }
            }
            int limit=q->getNumOfBlocks();
            for(int i=0;i<limit;i++)
            {
                q->getBlock(i,1);
                Block* block_ptr=mymem.getBlock(1);
                Schema myschema=q->getSchema();
                for(int j=0;j<myschema.getTuplesPerBlock();j++)
                {
                    Tuple tuple=block_ptr->getTuple(j);
                    if(!tuple.isNull())
                    {
                        if(satisfycondition(tuple,p->children[fromposition+3],false,NULL,myschema_manager)) 
                        {
                            //Handle select statement inside insertstatement 
                            if(withininsert)
                            {
                                newtuplenum++;
                                Block* resspace=mymem.getBlock(0);
                                if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0) resspace->appendTuple(tuple);
                                else
                                {
                                    resspace->appendTuple(tuple);
                                    insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                                    resspace->clear();
                                }
                            }
                            else
                            {
                                //All the attributes should be displayed with *.
                                if(column[0]=="*")
                                {
                                    cout<<tuple;
                                    cout<<endl;
                                }
                                //Only selected attribute will be displayed.
                                else
                                {
                                    for(int k=0;k<column.size();k++)
                                    {
                                        cout<<*(tuple.getField(column[k]).str);
                                        cout<<"    ";
                                    }
                                    cout<<endl;
                                }
                            }
                        }
                    }
                }
            }
        }
        //No WHERE statement. All the tuples will be displayed.
        else
        {
            Relation* q=myschema_manager.getRelation(p->children[fromposition+1]->children[0]->children[0]->value);
            vector<string> column=projectfield(p->children[fromposition-1]);                      
            if(!withininsert)
            {
                if(column[0]=="*")
                {
                    vector<string> field_names=q->getSchema().getFieldNames();
                    for(int i=0;i<field_names.size();i++) cout<<field_names[i]<<"\t";
                    cout<<endl;
                }
                else
                {
                    for(int k=0;k<column.size();k++) cout<<column[k]<<"\t";
                    cout<<endl;                
                }
            }
            int limit=q->getNumOfBlocks();
            for(int i=0;i<limit;i++)
            {
                q->getBlock(i,1);
                Block* block_ptr=mymem.getBlock(1);
                Schema myschema=q->getSchema();
                for(int j=0;j<myschema.getTuplesPerBlock();j++)
                {
                    Tuple tuple=block_ptr->getTuple(j);
                    if(!tuple.isNull())
                    {
                        //Handle select statement inside insertstatement.
                        if(withininsert)
                        {
                            newtuplenum++;
                            Block* resspace=mymem.getBlock(0);
                            if((newtuplenum%insertinto->getSchema().getTuplesPerBlock())!=0) resspace->appendTuple(tuple);
                            else
                            {
                                resspace->appendTuple(tuple);
                                insertinto->setBlock(insertinto->getNumOfBlocks(),0);
                                resspace->clear();
                            }
                        }
                        else
                        {
                            vector<string> column=projectfield(p->children[fromposition-1]);
                            if(column[0]=="*")
                            {
                                cout<<tuple;
                                cout<<endl;
                            }
                            else
                            {
                                for(int k=0;k<column.size();k++)
                                {
                                    if(tuple.getSchema().getFieldType(column[k])==INT) cout<<tuple.getField(column[k]).integer;
                                    else cout<<*(tuple.getField(column[k]).str);
                                    cout<<"\t";
                                }
                                cout<<endl;
                            }
                        }
                    }
                }
            }                    
        }*/
    }
    
    vector<string> projectfield(Node* p)
    {
        vector<string> res;
        if(p->children[0]->value=="*")
        {
            res.push_back("*");
            return res;
        }
        else
        {
            findfields(p,res);
            return res;
        }
    }
    
    void findfields(Node* p,vector<string>& res)   //should be optimized for multipletable later
    {
        if(p->value=="column_name")
        {
            if(p->childnum==1) res.push_back(p->children[0]->children[0]->value);
            else res.push_back(p->children[1]->children[0]->value);
            return;
        }
        for(int i=0;i<p->childnum;i++)
        {
            findfields(p->children[i],res);
        }
    }
    
    bool satisfycondition(Tuple tuple,Node* p,bool multitable,Node* qa,SchemaManager& myschema_manager)
    {
        vector<Node*> q;
        findconditions(q,p);
        vector<string> r;
        findbooleanops(r,p);
        if(r.size()==0) 
        {
            return singlecondition(tuple,q[0],multitable,qa,myschema_manager);
        }
        else
        {
            return testcomplexcondition(tuple,r,q,r.size(),multitable,qa,myschema_manager);
        }
    }
    
    bool testcomplexcondition(Tuple tuple,vector<string> r,vector<Node*> q,int i,bool multitable,Node* qa,SchemaManager& myschema_manager)
    {
        if(i==0) return singlecondition(tuple,q[0],multitable,qa,myschema_manager);
        if(r[i-1]=="AND") return (testcomplexcondition(tuple,r,q,i-1,multitable,qa,myschema_manager) && singlecondition(tuple,q[i],multitable,qa,myschema_manager));
        if(r[i-1]=="OR") return (testcomplexcondition(tuple,r,q,i-1,multitable,qa,myschema_manager) || singlecondition(tuple,q[i],multitable,qa,myschema_manager));        
    }
    
    bool singlecondition(Tuple& tuple,Node* p,bool multitable,Node* q,SchemaManager& myschema_manager)
    {
        while(p->value!="boolean_factor") p=p->children[0];
        bool numbercomp=false;
        isnumbercomp(numbercomp,p,multitable,tuple,myschema_manager);
        if(numbercomp)
        {
            int value1=numcomprand(p->children[0],tuple,multitable,q);
            int value2=numcomprand(p->children[2],tuple,multitable,q);
            if(p->children[1]->children[0]->value=="=")
            {
                return value1==value2;
            }
            else
            {
                if(p->children[1]->children[0]->value==">")
                {
                    return value1>value2;
                }
                else
                {
                    return value1<value2;
                }
            }            
        }
        else
        {
            string value1=stringcomprand(p->children[0],tuple,multitable,q);
            string value2=stringcomprand(p->children[2],tuple,multitable,q);
            if(p->children[1]->children[0]->value=="=")
            {
                return value1==value2;
            }
            else
            {
                if(p->children[1]->children[0]->value==">")
                {
                    return value1>value2;
                }
                else
                {
                    return value1<value2;
                }
            }
        }
        return true;
    }
    
    void isnumbercomp(bool& numbercomp,Node* p,bool multitable,Tuple& tuple,SchemaManager& myschema_manager)
    {
        if(p->value=="integer")
        {
            numbercomp=true;
            return;
        }
        if(p->value=="column_name")
        {
            if(p->childnum==1)
            {
                if(tuple.getSchema().getFieldType(p->children[0]->children[0]->value)==INT) numbercomp=true;
            }
            else
            {
                if(myschema_manager.getRelation(p->children[0]->children[0]->value)->getSchema().getFieldType(p->children[1]->children[0]->value)==INT) numbercomp=true;
            }
        }
        for(int i=0;i<p->childnum;i++) isnumbercomp(numbercomp,p->children[i],multitable,tuple,myschema_manager);
    }
    
    int numcomprand(Node* p,Tuple tuple,bool multitable,Node* q)
    {
        if(p->childnum==1)
        {
            if(p->children[0]->children[0]->value=="column_name") 
            {
                if(p->children[0]->children[0]->childnum==1) return tuple.getField(p->children[0]->children[0]->children[0]->children[0]->value).integer;
                else
                {
                    for(int i=0;i<q->involvedtable.size();i++)
                    {
                        if(p->children[0]->children[0]->children[0]->children[0]->value==q->involvedtable[i] && p->children[0]->children[0]->children[1]->children[0]->value==q->fieldname[i])
                        {
                            return tuple.getField(i).integer;
                        }
                    }
                    for(int i=0;i<q->involvedtable.size();i++)
                    {
                        if(p->children[0]->children[0]->children[1]->children[0]->value==q->fieldname[i])
                        {
                            return tuple.getField(i).integer;
                        }
                    }
                }
            }
            else return atoi(p->children[0]->children[0]->children[0]->value.c_str());
        }
        else
        {
            int value1;
            int value2;
            if(p->children[0]->children[0]->value=="column_name") 
            {
                if(p->children[0]->children[0]->childnum==1) value1=tuple.getField(p->children[0]->children[0]->children[0]->children[0]->value).integer;
                else
                {
                    bool completematch=false;
                    for(int i=0;i<q->involvedtable.size();i++)
                    {
                        if(p->children[0]->children[0]->children[0]->children[0]->value==q->involvedtable[i] && p->children[0]->children[0]->children[1]->children[0]->value==q->fieldname[i])
                        {
                            value1=tuple.getField(i).integer;
                            completematch=true;
                        }
                    }
                    if(!completematch)
                    {
                        for(int i=0;i<q->involvedtable.size();i++)
                        {
                            if(p->children[0]->children[0]->children[1]->children[0]->value==q->fieldname[i]) value1=tuple.getField(i).integer;
                        }
                    }
                }
            }
            else value1=atoi(p->children[0]->children[0]->children[0]->value.c_str());
            if(p->children[2]->children[0]->value=="column_name") 
            {
                if(p->children[2]->children[0]->childnum==1) value2=tuple.getField(p->children[2]->children[0]->children[0]->children[0]->value).integer;
                else
                {
                    bool completematch=false;
                    for(int i=0;i<q->involvedtable.size();i++)
                    {
                        if(p->children[2]->children[0]->children[0]->children[0]->value==q->involvedtable[i] && p->children[2]->children[0]->children[1]->children[0]->value==q->fieldname[i])
                        {
                            value2=tuple.getField(i).integer;
                            completematch=true;
                        }
                    }
                    if(!completematch)
                    {
                        for(int i=0;i<q->involvedtable.size();i++)
                        {
                            if(p->children[2]->children[0]->children[1]->children[0]->value==q->fieldname[i]) value2=tuple.getField(i).integer;
                        }
                    }
                }
            }
            else value2=atoi(p->children[2]->children[0]->children[0]->value.c_str());
            if(p->children[1]->value=="+")
            {
                return value1+value2;
            }
            else
            {
                if(p->children[1]->value=="-")
                {
                    return value1-value2;
                }
                else
                {
                    return value1*value2;
                }
            }
        }
    }
    
    string stringcomprand(Node* p,Tuple tuple,bool multitable,Node* q)
    {
        if(p->childnum==1)
        {
            if(p->children[0]->children[0]->value=="column_name")
            {
                if(p->children[0]->children[0]->childnum==1) return *(tuple.getField(p->children[0]->children[0]->children[0]->children[0]->value).str);
                else
                {
                    for(int i=0;i<q->involvedtable.size();i++)
                    {
                        if(p->children[0]->children[0]->children[0]->children[0]->value==q->involvedtable[i] && p->children[0]->children[0]->children[1]->children[0]->value==q->fieldname[i])
                        {
                            return *(tuple.getField(i).str);
                        }
                    }
                    for(int i=0;i<q->involvedtable.size();i++)
                    {
                        if(p->children[0]->children[0]->children[1]->children[0]->value==q->fieldname[i]) return *(tuple.getField(i).str);
                    }
                }
            }
            else return p->children[0]->children[0]->children[0]->value;
        }
    }    
    
    void findconditions(vector<Node*>& q,Node* p)
    {
        if(p->value=="boolean_factor") q.push_back(p);
        for(int i=0;i<p->childnum;i++) findconditions(q,p->children[i]);
    }
    
    void findbooleanops(vector<string>& r,Node* p)
    {
        if(p->value=="AND" || p->value=="OR")    r.push_back(p->value);
        for(int i=0;i<p->childnum;i++)    findbooleanops(r,p->children[i]);
    }
    
    void inserttuples(Node* p,SchemaManager& myschema_manager,MainMemory& mymem,RelationStat& myrelationstat) //not finished
    {
        if(p->children[4]->children[0]->value=="VALUES")
        {
            string relationname;
            vector<string> field_names;
            vector<string> field_types;
            vector<string> field_values;
            relationname=p->children[2]->children[0]->value;
            getinsertfields(field_names,p->children[3]);
            getinsertvalues(field_types,field_values,p->children[4]->children[1]);
            myrelationstat.insertnewtuple(relationname,field_names,field_values);
            Relation* q=myschema_manager.getRelation(relationname);
            Tuple tuple=q->createTuple();
            for(int i=0;i<field_names.size();i++)
            {
                if(field_types[i]=="NULL") tuple.setField(field_names[i],0);
                else
                {
                    if(field_types[i]=="STR20") tuple.setField(field_names[i],field_values[i]);
                    else
                    {
                        tuple.setField(field_names[i],atoi(field_values[i].c_str()));
                    }
                }
            }
            appendTupleToRelation(q,mymem,5,tuple);
            cout<<"----------One tuple is inserted into table "<<p->children[2]->children[0]->value<<".----------"<<endl;
        }
        else
        {//This function only handle that selection is picked out from the table into which insertion will happen. Also, all the attributes should be picked out.
            int newtuplenum=0;
            selectstatement(p->children[4]->children[0],myschema_manager,mymem,true,myschema_manager.getRelation(p->children[2]->children[0]->value),newtuplenum);
            if(newtuplenum==0) cout<<"----------No tuple is inserted into table "<<p->children[2]->children[0]->value<<"."<<"----------"<<endl;
            else 
            {
                if(newtuplenum==1) cout<<"----------One tuple is inserted into table "<<p->children[2]->children[0]->value<<"."<<"----------"<<endl;
                else cout<<"----------"<<newtuplenum<<" tuples are inserted into table "<<p->children[2]->children[0]->value<<"."<<"----------"<<endl;
            }
        }
    }
    
    void getinsertfields(vector<string>& field_names,Node* p)
    {
        if(p->value=="attribute_name")
        {
            field_names.push_back(p->children[0]->value);
            return;
        }
        for(int i=0;i<p->childnum;i++)
        {
            getinsertfields(field_names,p->children[i]);
        }
    }
    
    void getinsertvalues(vector<string>& field_types,vector<string>& field_values,Node* p)
    {
        if(p->value=="value")
        {
            if(p->children[0]->value=="NULL")
            {
                field_values.push_back("NULL");
                field_types.push_back("NULL");
            }
            else
            {
                if(p->children[0]->value=="integer") 
                {
                    field_types.push_back("INT");
                    field_values.push_back(p->children[0]->children[0]->value);
                }
                else
                {
                    field_values.push_back(p->children[0]->children[0]->value);
                    field_types.push_back("STR20");                    
                }
            }
        }
        for(int i=0;i<p->childnum;i++) getinsertvalues(field_types,field_values,p->children[i]);
    }
    
    void mygetschema(vector<string>& field_names,vector<enum FIELD_TYPE>& field_types,Node* p)
    {
        if(p->value=="attribute_type_list")
        {
            field_names.push_back(p->children[0]->children[0]->value);
            enum FIELD_TYPE field_type;
            if(p->children[1]->children[0]->value=="INT") field_type=INT;
            else field_type=STR20;
            field_types.push_back(field_type);
        }
        for(int i=0;i<p->childnum;i++)
        {
            mygetschema(field_names,field_types,p->children[i]);
        }
    }
};