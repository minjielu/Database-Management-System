MyDatabase: StorageManager.o 
	g++ -o myDatabase StorageManager.o myDatabase.cc
	
StorageManager.o: Block.h Disk.h Field.h MainMemory.h Relation.h Schema.h SchemaManager.h Tuple.h Config.h
	g++ -c StorageManager.cpp	

clean:
	rm *.o myDatabase
