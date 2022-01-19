#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <getopt.h>
#include <sys/stat.h>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <algorithm>
#include <utility>
using std::string;
using std::vector;
using std::array;
using std::set;
using std::map;
using std::min;
using std::max;
using std::pair;

typedef unsigned char UC;
typedef unsigned int uint32;
typedef signed long long int int64;
typedef unsigned long long int uint64;
template<class T> struct array2d {
  size_t rows,cols;
  vector<T> data;
  array2d(){}
  array2d(size_t r, size_t c):rows(r),cols(c),data(r*c){}
  void resize(size_t r, size_t c){rows=r;cols=c;data.resize(r*c);}
  T* operator[](size_t index){return &data[index*cols];}// First level indexing
};
const int infinity=1000000000;
const char*outdir=0;
int showtop=0,s2mult=10;
int minoptcacheremdepth=2;
int minlboundcacheremdepth=3;
#define MAXDEPTH 100
typedef vector<int> list;
typedef pair<list,list> list2;

// mode=0 ==> can use any word
// mode=1 ==> can only use nice words (2315 list)
// mode=2 ==> can only use currently possible word (="hard mode")
int mode=0,maxg=0,n0=0,n1=0,nth=1,n0th=-1;
int maxguesses=6;
int64 cachestats[MAXDEPTH+1]={0},cachemiss[MAXDEPTH+1]={0},entrystats[MAXDEPTH+1][5]={0};
array2d<int64> optstats;
map<list2,int> opt[MAXDEPTH+1],lbound[MAXDEPTH+1];
array2d<UC> sc,testwords,hiddenwords;
const char*toplist=0,*topword=0;
int64 totentries=0,nextmemcheck=0,memcheckinterval=100000;
double cachememlimit=0.5;// Approximate total memory limit for opt and lbound caches in GB
double nextcheckpoint=0,checkpointinterval=3600;
int humanorder[243];// Order the 243 scores in alphabetical order
array2d<uint64> multiset64;
int greenyellowpos[243];
uint32 greenmask25bit[243];
vector<uint32> testwords25bit;
int depthonly=0;

double cpu(){return clock()/double(CLOCKS_PER_SEC);}
int timings=0;
#define MAXTIM 50
double ncpu[MAXTIM]={0},lcpu[MAXTIM]={0},tcpu[MAXTIM]={0};
void tick(int i){if(timings)lcpu[i]=cpu();}
void tock(int i){if(timings){ncpu[i]+=1;tcpu[i]+=cpu()-lcpu[i];}}
void prtim(){
  int i;
  if(ncpu[0]==0)return;
  double x=tcpu[0]/ncpu[0];
  for(i=0;i<MAXTIM;i++)if(ncpu[i]){
    double t=tcpu[i]-ncpu[i]*x;
    printf("Time %2d: CPU %12gs / %12g = %12gus\n",i,t,ncpu[i],t/ncpu[i]*1e6);
  }
}

// Split string into a sequence of substrings using any character from sep (default whitespace) as a separator.
vector<string> split(string in,string sep=" \r\t\n\f\v"){
  size_t i,j,p=0;
  vector<string> rv;
  while(1){
    i=in.find_first_not_of(sep,p);if(i==string::npos)i=in.size();
    j=in.find_first_of(sep,i);if(j==string::npos)j=in.size();
    if(i==j)return rv;
    rv.push_back(in.substr(i,j-i));
    p=j;
  }
}

array2d<UC> load(const char *fn){
  FILE *fp=fopen(fn,"r");assert(fp);
  char l[1000];
  vector<string> tmp;
  array2d<UC> ret;
  while(fgets(l,1000,fp))tmp.push_back(l);
  fclose(fp);
  int n=tmp.size();
  ret.resize(n,5);
  for(int i=0;i<n;i++)for(int j=0;j<5;j++)ret[i][j]=tolower(tmp[i][j])-'a';
  return ret;
}

string decword(UC*w){
  int i;
  char ret[6];
  ret[5]=0;
  for(i=0;i<5;i++)ret[i]='a'+w[i];
  return string(ret);
}

string decscore(int s){
  char ret[6];
  ret[5]=0;
  for(int i=0;i<5;i++){ret[i]="BYG"[s%3];s/=3;}
  return string(ret);
}

// Ternary, L->H, 0=black, 1=yellow, 2=green
int score(UC*test,UC*hidden){
  UC t[5],h[5];
  memcpy(t,test,5);
  memcpy(h,hidden,5);
  int k,l,s=0,w;

  // Greens
  for(k=0,w=1;k<5;k++){
    if(t[k]==h[k]){t[k]=254;h[k]=255;s+=2*w;}
    w*=3;
  }

  // Yellows
  for(k=0,w=1;k<5;k++){
    for(l=0;l<5;l++)if(t[k]==h[l]){s+=w;h[l]=255;break;}
    w*=3;
  }
      
  //printf("%s %s %s\n",decword(testwords[i]).c_str(),decword(hiddenwords[j]).c_str(),decscore(s).c_str());

  return s;
}

void writeoptstats(){
  if(!outdir)return;
  int i;
  FILE*fp=fopen((string(outdir)+"/optstats").c_str(),"w");assert(fp);
  for(i=0;i<=int(hiddenwords.rows);i++)if(optstats[i][0])fprintf(fp,"%4d   %12lld %12lld %10.3f\n",i,optstats[i][0],optstats[i][1],optstats[i][1]/double(optstats[i][0]));
  fclose(fp);
}

void writewordlist(array2d<UC>&wl,string fn){
  if(!outdir)return;
  string path=outdir+("/"+fn);
  FILE*fp=fopen(path.c_str(),"w");assert(fp);
  int i;
  for(i=0;i<int(wl.rows);i++){
    fprintf(fp,"%s\n",decword(wl[i]).c_str());
  }
  fclose(fp);
}

void readmap(string path,map<list,int>*ret,int maxd=MAXDEPTH){
  FILE*fp=fopen(path.c_str(),"r");assert(fp);
  char l[100000];
  while(fgets(l,100000,fp)){
    vector<string> v0=split(l,":");
    int d=maxguesses-stoi(v0[0]);
    if(d<0||d>maxd||d>=MAXDEPTH)continue;
    int v=stoi(v0[2]);
    vector<string> v1=split(v0[1]," ");
    list vi;
    for(string &s:v1)vi.push_back(stoi(s));
    ret[d][vi]=v;
  }
  fclose(fp);
}

void loadcachefromdir(string dir){
  /*
  printf("Loading cache from directory \"%s\"...",dir.c_str());fflush(stdout);
  readmap(dir+"/exactcache",opt,maxguesses-minoptcacheremdepth);
  readmap(dir+"/lboundcache",lbound,maxguesses-minlboundcacheremdepth);
  printf("...done\n");
  */
}

void writemap(map<list,int>*m,string fn){
  int d;
  if(!outdir)return;
  string path=outdir+("/"+fn);
  FILE*fp=fopen(path.c_str(),"w");assert(fp);
  for(d=0;d<=MAXDEPTH;d++){
    for(auto &pair:m[d]){
      fprintf(fp,"%d :",maxguesses-d);
      for(int t:pair.first)fprintf(fp," %d",t);
      fprintf(fp," : %d\n",pair.second);
    }
  }
  fclose(fp);
 }

void savecache(){
  /*
  if(!outdir)return;
  writemap(opt,"exactcache");
  writemap(lbound,"lboundcache");
  */
}

int readoptcache(int depth,list&oktestwords,list&hwsubset){
  if(maxguesses-depth>=minoptcacheremdepth){
    map<list2,int>::iterator it;
    it=opt[depth].find(list2(oktestwords,hwsubset));
    if(it!=opt[depth].end()){
      cachestats[depth]++;
      return it->second;
    }else{
      cachemiss[depth]++;
    }
  }
  return -1;
}

int readlboundcache(int depth,list&oktestwords,list&hwsubset){
  if(maxguesses-depth>=minlboundcacheremdepth){
    map<list2,int>::iterator it;
    it=lbound[depth].find(list2(oktestwords,hwsubset));
    if(it!=lbound[depth].end()){
      return it->second;
    }
  }
  return -1;
}

void writeoptcache(int depth,list&oktestwords,list&hwsubset,int v){
  if(maxguesses-depth>=minoptcacheremdepth)opt[depth][list2(oktestwords,hwsubset)]=v;
}

void writelboundcache(int depth,list&oktestwords,list&hwsubset,int v){
  if(maxguesses-depth>=minlboundcacheremdepth)lbound[depth][list2(oktestwords,hwsubset)]=v;
}

void prwordlist(list&wl){
  for(int i:wl)printf("%s ",decword(testwords[i]).c_str());
  printf("\n");
}

void inithardmodecheck(){
  int a,g,i,j,p,s,nt=testwords.rows;;
  multiset64.resize(nt,32);
  testwords25bit.resize(nt);
  for(i=0;i<nt;i++){
    uint32 t=0;
    for(p=0;p<5;p++)t|=testwords[i][p]<<(5*p);
    testwords25bit[i]=t;
  }
  for(s=0;s<243;s++){
    int s1=s,u=0;
    uint32 v=0;
    for(p=0;p<5;p++){
      if(s1%3==2)v|=31<<(5*p);
      if(s1%3)u+=1<<p;
      s1/=3;
    }
    greenyellowpos[s]=u;
    greenmask25bit[s]=v;
  }
  for(j=0;j<nt;j++){
    for(g=0;g<32;g++){
      UC mult[26];
      memset(mult,0,26);
      for(p=0;p<5;p++)if((g>>p)&1)mult[testwords[j][p]]++;
      uint64 t=0;
      for(a=0;a<26;a++){assert(mult[a]<4);t|=uint64(mult[a])<<(a*2);}
      multiset64[j][g]=t;
    }
  }
}

// Is j an allowable testword to choose given that word i has scored s?
// i = past test word
// s = score of past test word
// j = test word we are determining the legality of
int okhard(int i,int s,int j){
  uint32 M=greenmask25bit[s];
  uint32 X=testwords25bit[i]&M;
  uint32 X1=testwords25bit[j]&M;
  if(X1!=X)return 0;
  uint64 Z=multiset64[i][greenyellowpos[s]];
  uint64 Z1=multiset64[j][31];
  // Bit twiddling to test if all entries (letter multiplicities) in Z1 are >= corresponding entries in Z
  return (((~Z1&Z)|(~(Z1^Z)&(Z1-Z)))&0xaaaaaaaaaaaaaaaaULL)==0;
}

// Input:
//   words = existing allowable test words
//   t = chosen test word
//   s = score of test word
//   t1 = hypothetical future test word
// Output:
//   new reduced set of allowable test words in hard mode
list filter(list&words,int t,int s){
  list ret;
  for(int t1:words)if(okhard(t,s,t1))ret.push_back(t1);
  if(0&&words.size()<=10){
    printf("XXX %s %s\n",decword(testwords[t]).c_str(),decscore(s).c_str());
    prwordlist(words);
    printf("-->\n");
    prwordlist(ret);
    printf("\n");
  }
  return ret;
}

int optimise(list oktestwords,list&hwsubset,int depth,int beta=infinity,int fast=0,int *rbest=0);

// Returns minimum_{s in considered strategies} sum_{h in hiddenwordsubset} (number of guesses strategy s requires for word h)
//      or -1 in fast mode, which means "Can't find a fast answer"
int optimise_inner(list&oktestwords,list&hwsubset,int depth,int beta=infinity,int fast=0,int *rbest=0){
  int i,j,k,n,s,t,nh=hwsubset.size(),remdepth=maxguesses-depth;
  assert(depth<MAXDEPTH);
  totentries++;
  entrystats[depth][0]++;
  if(rbest)*rbest=-1;
  if(remdepth<=0)return beta;
  if(depth>0&&2*nh-1>=beta)return beta;
  if(depth>0&&nh==1){if(rbest)*rbest=hwsubset[0];return 1;}
  if(remdepth<=1)return beta;
  if(depth>0&&nh==2){if(rbest)*rbest=hwsubset[0];return 3;}
  entrystats[depth][1]++;
  if(fast==1)return -1;
  if(!(rbest||(depth==0&&showtop))){int v=readoptcache(depth,oktestwords,hwsubset);if(v>=0)return v;}
  entrystats[depth][2]++;
  tick(0);tock(0);// calibration
  if(totentries>=nextmemcheck){
    int d;
    int64 n=0;
    for(d=0;d<=MAXDEPTH;d++)n+=opt[d].size()+lbound[d].size();
    if(n*1500>=cachememlimit*1e9){
      for(d=0;d<=MAXDEPTH;d++){opt[d].clear();lbound[d].clear();}
    }
    nextmemcheck+=memcheckinterval;
  }
  
  int nt=oktestwords.size();//(mode==0 ? testwords.rows : (mode==1 ? hiddenwords.rows : hwsubset.size()));
  int thr;
  vector<uint64> s2a(nt);
  if(depth==0&&(toplist||topword)){
    int start=0,step=1;
    array2d<UC> fwl;
    if(toplist){
      vector<string> tlf=split(toplist,",");
      fwl=load(tlf[0].c_str());
      if(tlf.size()>=2)start=std::stoi(tlf[1]);
      if(tlf.size()>=3)step=std::stoi(tlf[2]);
    }else{
      fwl.resize(1,5);
      for(int j=0;j<5;j++)fwl[0][j]=tolower(topword[j])-'a';
    }
    int r=0;
    for(j=start;j>=0&&j<int(fwl.rows);j+=step){
      for(i=0;i<nt;i++){
        //if(mode<2)t=i; else t=hwsubset[i];// Currently redundant
        t=oktestwords[i];
        if(!memcmp(fwl[j],testwords[t],5))s2a[r++]=uint64(j)<<32|t;
      }
    }
    nt=r;
    s2a.resize(nt);
    thr=nt;
  }else{
    int count[243];
    tick(5);
    // Check for perfect test word, which would mean we don't need to consider others
    if(depth>0){
      for(int t:hwsubset){
        memset(count,0,sizeof(count));
        for(j=0;j<nh;j++){
          int c=(++count[sc[t][hwsubset[j]]]);
          if(c==2)goto nlt;
        }
        writeoptcache(depth,oktestwords,hwsubset,2*nh-1);
        if(rbest)*rbest=t;
        return 2*nh-1;
      nlt:;
      }
    }
    tock(5);
    if(fast==2)return -1;
    tick(1);
    for(i=0;i<nt;i++){
      //if(mode<2)t=i; else t=hwsubset[i];
      t=oktestwords[i];
      memset(count,0,sizeof(count));
      for(j=0;j<nh;j++)count[sc[t][hwsubset[j]]]++;
      int s2=0,t2=0;
      for(s=0;s<242;s++){s2+=count[s]*count[s];t2+=(count[s]==0);}
      // Check for 2nd perfect test word, which means we don't need to consider the rest
      if(depth>0&&count[242]==0&&s2==nh){
        writeoptcache(depth,oktestwords,hwsubset,2*nh);
        if(rbest)*rbest=t;
        return 2*nh;
      }
      s2a[i]=int64(s2mult*s2+nh*t2)<<32|t;
    }
    tock(1);
    // Having not found a perfect testword that splits into singletons, we must require at least 3 guesses in worst case.
    if(depth>0&&remdepth<=2){
      writeoptcache(depth,oktestwords,hwsubset,infinity);
      return infinity;
    }
    if(depth==0&&n0th>0)thr=n0th; else thr=nth;
    if(depth<=2)std::sort(s2a.begin(),s2a.end()); else if(thr-1<nt)std::nth_element(&s2a[0],&s2a[thr-1],&s2a[nt]);
  }

  int mi=beta,best=-1,exact=0;
  int clip=beta;
  double cpu0=cpu();
  double cpu1=cpu0;
  for(i=0;i<min(thr,nt);i++){
    int val=s2a[i]>>32;
    int t=s2a[i]&((1ULL<<32)-1);
    list equiv[243];
    tick(2);
    for(j=0;j<nh;j++){
      int h=hwsubset[j];
      s=sc[t][h];
      equiv[s].push_back(h);
    }
    tock(2);
    int64 tot=0;
    int ind[243],lb[243];
    // First loop over the partition finding out very fast (fast=1) information if available
    tick(3);
    for(n=s=0;s<243&&tot<clip;s++){
      int sz=equiv[s].size();
      if(sz){
        if(s==242){tot+=1;continue;}
        // Don't need to filter here because oktestwords isn't used in fastmode 1
        int o=optimise(oktestwords,equiv[s],depth+1,clip-tot-sz,1);
        if(o>=0){tot+=sz+o;continue;}
        lb[s]=3*sz-1;
        tot+=lb[s];
        ind[n++]=s;
      }
    }
    tock(3);
    // Then loop over the partition finding out medium fast (fast=2) information if available
    list filtered[243];
    if(tot<clip){
      int k,m;
      tick(4);
      for(k=m=0;k<n&&tot<clip;k++){
        s=ind[k];
        int sz=equiv[s].size();
        assert(s<242);
        if(lb[s]==3*sz-1){
          tot-=lb[s];
          filtered[s]=filter(oktestwords,t,s);
          int o=optimise(filtered[s],equiv[s],depth+1,clip-tot-sz,2);
          if(o>=0){int inc=sz+o;assert(inc>=lb[s]);tot+=inc;continue;}
          lb[s]=3*sz;
          {int v=readlboundcache(depth+1,filtered[s],equiv[s]);if(v>=0)lb[s]=max(lb[s],sz+v);}
          tot+=lb[s];
        }
        ind[m++]=s;
      }
      n=m;
      tock(4);
      // '>' appears to work better at finding new best testwords, '<' at disproving bad testwords when there is a decent beta bound
      auto cmp=[&equiv](const int&s0,const int&s1)->bool{return equiv[s0].size()<equiv[s1].size();};
      std::sort(ind,ind+n,cmp);
    }
    // Now loop over the remaining partition doing a full search
    tick(10+depth);
    for(k=0;k<n&&tot<clip;k++){
      s=ind[k];
      int sz=equiv[s].size();
      int inc;
      assert(s<242);
      tot-=lb[s];
      if(filtered[s].size()==0)filtered[s]=filter(oktestwords,t,s);
      inc=sz+optimise(filtered[s],equiv[s],depth+1,clip-tot-sz);
      assert(inc>=lb[s]);
      tot+=inc;
    }
    tock(10+depth);
    assert(tot>=0);
    if(tot>=infinity/2)tot=infinity;
    if(depth==0&&!rbest){
      double cpu2=cpu();
      printf("First guess %s %s= %lld  heuristic = %7d    dCPU = %9.2f   CPU = %9.2f\n",
             decword(testwords[t]).c_str(),tot<clip||tot==infinity?" ":">",tot,val,cpu2-cpu1,cpu2-cpu0);
      cpu1=cpu2;
      fflush(stdout);
    }
    // tot<clip implies all calls to optimise() returned an answer < the beta used to call it, which implies they are all exact
    // And if it's exact for one testword, then the final answer has to be exact because either hit a new exact word, or all subsequent words are >= it in score.
    if(tot<clip)exact=1;
    if(tot<mi){
      mi=tot;best=t;
      if(!(depth==0&&showtop))clip=mi;
    }
    if(depth==0){
      double cpu3=cpu();
      if(cpu3>=nextcheckpoint){
        writeoptstats();
        savecache();
        nextcheckpoint+=checkpointinterval;
      }
    }
    if(depthonly&&!(depth==0&&showtop)&&mi<infinity/2)break;
  }
  if(depth==0&&!rbest)printf("Best first guess = %s\n",best>=0?decword(testwords[best]).c_str():"no-legal-guess");
  if(mi>=infinity/2){mi=infinity;exact=1;}
  if(exact){optstats[nh][0]++;optstats[nh][1]+=mi;}
  if(exact)writeoptcache(depth,oktestwords,hwsubset,mi);
  if(!exact)writelboundcache(depth,oktestwords,hwsubset,mi);
  if(rbest)*rbest=best;
  return mi;
}

int optimise(list oktestwords,list&hwsubset,int depth,int beta,int fast,int *rbest){
  int o=optimise_inner(oktestwords,hwsubset,depth,beta,fast,rbest);
  if(o==-1)return -1;
  return min(o,beta);
}

int printtree(list oktestwords,list&hwsubset,int depth,FILE*tfp){
  int i,j,o,s,best;
  int nh=hwsubset.size();

  o=optimise(oktestwords,hwsubset,depth,infinity,0,&best);
  if(best==-1){
    fprintf(tfp,"IMPOSSIBLE\n");
    return o;
  }
  fprintf(tfp,"%s ",decword(testwords[best]).c_str());
  
  list equiv[243];
  for(j=0;j<nh;j++){
    int h=hwsubset[j];
    s=sc[best][h];
    equiv[s].push_back(h);
  }
  int first=1;
  for(i=0;i<243;i++){
    s=humanorder[i];
    if(equiv[s].size()){
      if(!first)for(j=0;j<depth*13+6;j++)fprintf(tfp," ");
      first=0;
      fprintf(tfp,"%s%d",decscore(s).c_str(),depth+1);
      if(s<242){
        fprintf(tfp," ");
        printtree(filter(oktestwords,best,s),equiv[s],depth+1,tfp);
      }else{
        fprintf(tfp,"\n");
      }
    }
  }
  return o;
}

int main(int ac,char**av){
  printf("Commit %s\n",COMMITDESC);
  int beta=infinity;
  const char*treefn=0,*loadcache=0;
  
  while(1)switch(getopt(ac,av,"b:dr:R:n:N:m:g:l:p:st:M:Tw:x:")){
    case 'b': beta=atoi(optarg);break;
    case 'd': depthonly=1;break;
    case 'l': loadcache=strdup(optarg);break;
    case 'n': nth=atoi(optarg);break;
    case 'N': n0th=atoi(optarg);break;
    case 'm': mode=atoi(optarg);break;
    case 'M': s2mult=atoi(optarg);break;
    case 'g': maxguesses=atoi(optarg);break;
    case 'p': treefn=strdup(optarg);break;
    case 'r': minoptcacheremdepth=atoi(optarg);break;
    case 'R': minlboundcacheremdepth=atoi(optarg);break;
    case 's': showtop=1;break;
    case 't': toplist=strdup(optarg);break;
    case 'T': timings=1;break;
    case 'w': topword=strdup(optarg);break;
    case 'x': outdir=strdup(optarg);break;
    case -1: goto ew0;
    default: fprintf(stderr,"Options: b=beta, d enables depth-only mode, n=nth, N=nth at top level, m=mode, g=max guesses, p=print tree filename, s enables showtop, t=toplist filename[,start[,step]], w=topword, T enables timings, x=outdir\n");exit(1);
  }
 ew0:;

  hiddenwords=load("wordlist_hidden");
  testwords=load("wordlist_all");
  //testwords=hiddenwords;
  optstats.resize(hiddenwords.rows+1,2);
  if(outdir)mkdir(outdir,0777);
  writewordlist(hiddenwords,"hiddenwords");
  writewordlist(testwords,"testwords");
  if(loadcache)loadcachefromdir(loadcache);
  for(int i=0;i<int(hiddenwords.rows);i++)assert(!memcmp(testwords[i],hiddenwords[i],5));
  
  int i,j,nt=testwords.rows,nh=hiddenwords.rows;
  sc.resize(nt,nh);
  for(i=0;i<nt;i++)for(j=0;j<nh;j++)sc[i][j]=score(testwords[i],testwords[j]);
  inithardmodecheck();
  list allhidden(nh),alltest(nt);
  for(j=0;j<nh;j++)allhidden[j]=j;
  for(j=0;j<nt;j++)alltest[j]=j;
  maxguesses=min(maxguesses,MAXDEPTH);
  for(i=0;i<243;i++)humanorder[i]=i;
  auto cmp=[](const int&i0,const int&i1)->bool{return decscore(i0)<decscore(i1);};
  std::sort(humanorder,humanorder+243,cmp);

  printf("nth = %d\n",nth);
  printf("n0th = %d\n",n0th);
  printf("mode = %d\n",mode);
  printf("maxguesses = %d\n",maxguesses);
  printf("beta = %d\n",beta);
  printf("showtop = %d\n",showtop);
  printf("top-level list = %s\n",toplist?toplist:"(not given)");
  printf("top-level word = %s\n",topword?topword:"(not given)");
  printf("s2mult = %d\n",s2mult);
  printf("depthonly = %d\n",depthonly);
  printf("tree filename = \"%s\"\n",treefn?treefn:"(not given)");
  printf("min{opt,lbound}cacheremdepths = %d %d\n",minoptcacheremdepth,minlboundcacheremdepth);
  fflush(stdout);
  double cpu0=cpu();
  int o;
  if(treefn){
    FILE*tfp=fopen(treefn,"w");assert(tfp);
    o=printtree(alltest,allhidden,0,tfp);
    fclose(tfp);
    printf("Written tree to file \"%s\"\n",treefn);
  }else{
    o=optimise(alltest,allhidden,0,beta);
  }
  printf("Best first guess score %s= %d\n",depthonly&&o<infinity?"<":"",o);
  printf("Average guesses reqd using best first guess = %.4f\n",o/double(nh));
  double cpu1=cpu()-cpu0;
  printf("Time taken = %.2fs\n",cpu1);
  for(i=0;i<=maxguesses;i++)if(cachestats[i]||entrystats[i][0])printf("Depth %2d: Entries = %12lld %12lld %12lld    Cache writes reads misses = %12lu %12lld %12lld\n",i,entrystats[i][0],entrystats[i][1],entrystats[i][2],opt[i].size(),cachestats[i],cachemiss[i]);
  printf("Rates per second:\n");
  for(i=0;i<=maxguesses;i++)if(cachestats[i]||entrystats[i][0])printf("Depth %2d: Entries = %12g %12g %12g    Cache writes reads misses = %12g %12g %12g\n",i,entrystats[i][0]/cpu1,entrystats[i][1]/cpu1,entrystats[i][2]/cpu1,opt[i].size()/cpu1,cachestats[i]/cpu1,cachemiss[i]/cpu1);
  writeoptstats();
  savecache();
  prtim();
}
