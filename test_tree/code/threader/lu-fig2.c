#include <pthread.h>

int mThread=0;
int start_main=0;
int __COUNT__ =0;


void* thread1(void* arg) { //nsThread::Init (mozilla/xpcom/threads/nsThread.cpp 1.30)

  int PR_CreateThread__RES = 1;
  start_main=1;
  { __VERIFIER_atomic_begin();
      if( __COUNT__ == 0 ) { // atomic check(0);
	mThread = PR_CreateThread__RES; 
	__COUNT__ = __COUNT__ + 1; 
      } else { assert(0); } 
    __VERIFIER_atomic_end();
  }
  if (mThread == 0) { return -1; }
  else { return 0; }
}


void* thread2(void* arg) { //nsThread::Main (mozilla/xpcom/threads/nsThread.cpp 1.30)

  int self = mThread;
  while (start_main==0);
  { __VERIFIER_atomic_begin();
      if( __COUNT__ == 1 ) { // atomic check(1);
	int rv = self; // self->RegisterThreadSelf();
	__COUNT__ = __COUNT__ + 1;
      } else { assert(0); } 
   __VERIFIER_atomic_end();
  }
  return NULL;
}

void main() {
  pthread_t t1, t2;

  pthread_create(&t1, NULL, thread1, NULL);
  pthread_create(&t2, NULL, thread2, NULL);
}
