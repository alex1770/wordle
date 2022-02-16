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
typedef unsigned int uint;
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
int showtop=0,s2mult=2;
int minoptcacheremdepth=2;
int minlboundcacheremdepth=3;
#define MAXDEPTH 100
typedef vector<short> list;
typedef pair<list,list> list2;

int maxg=0,n0=0,n1=0,nth=-1,n0th=-1;
int maxguesses=6;
int64 cachewrites[MAXDEPTH+1]={0},cachereads[MAXDEPTH+1]={0},cachemiss[MAXDEPTH+1]={0},entrystats[MAXDEPTH+1][5]={0};
array2d<int64> optstats;
map<list2,int> opt[MAXDEPTH+1],lbound[MAXDEPTH+1];
int64 cachesize[MAXDEPTH+1]={0};
array2d<UC> sc;// wordle score array (map from testword, hiddenword -> colour score as a number in [0,243))
vector<string> testwords,hiddenwords;
list alltest,allhidden;
const list emptylist;
const char*toplist=0,*topword=0;
int64 totentries=0,nextcheck=0,checkinterval=1000000;
double cachememlimit=2;// Approximate total memory limit for opt and lbound caches in GB
double nextcheckpoint=0,checkpointinterval=-1;
int humanorder[243];// Order the 243 scores in alphabetical order
array2d<uint64> multiset64;
int greenyellowpos[243];
uint greenmask25bit[243];
vector<uint> testwords25bit;
int depthonly=0;
int prl=-1;
const char*wordlist_hidden_name="wordlist_hidden";
const char*wordlist_all_name="wordlist_all";
vector<list> wordnum2endgame;
int numendgames;
unsigned int minendgamecount=4;
int hardmode=0;
int exhaust=0;// With exhaustive search certain kinds of reasoning become valid, so we want to keep a note of whether we're exhausting or not.
struct state {
  int depth;
  list oktestwords,hwsubset;
};
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

void prs(int n){
  for(int i=0;i<n;i++)printf(" ");
}

vector<string> load(const char *fn){
  FILE *fp=fopen(fn,"r");assert(fp);
  char l[1000];
  vector<string> ret;
  while(fgets(l,1000,fp)){l[5]=0;ret.push_back(l);}
  fclose(fp);
  return ret;
}

string decscore(int s){
  char ret[6];
  ret[5]=0;
  for(int i=0;i<5;i++){ret[i]="BYG"[s%3];s/=3;}
  return string(ret);
}

int encscore(string st){
  std::transform(st.begin(), st.end(), st.begin(), [](unsigned char c){ return std::toupper(c); });
  int s=0;
  for(int i=4;i>=0;i--){
    if(!(st[i]=='B'||st[i]=='Y'||st[i]=='G')){fprintf(stderr,"Illegal score string %s\n",st.c_str());exit(1);}
    s=3*s+(st[i]=='Y')+2*(st[i]=='G');
  }
  return s;
}

// Ternary, L->H, 0=black, 1=yellow, 2=green
int score(string &test,string &hidden){
  char t[5],h[5];
  memcpy(t,test.c_str(),5);
  memcpy(h,hidden.c_str(),5);
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
      
  //printf("%s %s %s\n",testwords[i].c_str(),hiddenwords[j].c_str(),decscore(s).c_str());

  return s;
}

void writeoptstats(){
  if(!outdir)return;
  int i;
  FILE*fp=fopen((string(outdir)+"/optstats").c_str(),"w");assert(fp);
  for(i=0;i<=int(hiddenwords.size());i++)if(optstats[i][0])fprintf(fp,"%4d   %12lld %12lld %10.3f\n",i,optstats[i][0],optstats[i][1],optstats[i][1]/double(optstats[i][0]));
  fclose(fp);
}

void writewordlist(list wl,string fn){
  if(!outdir)return;
  string path=outdir+("/"+fn);
  FILE*fp=fopen(path.c_str(),"w");assert(fp);
  for(int t:wl)fprintf(fp,"%s\n",testwords[t].c_str());
  fclose(fp);
}

void readmap(string path,map<list2,int>*ret,int maxd=MAXDEPTH){
  FILE*fp=fopen(path.c_str(),"r");assert(fp);
  char l[100000];
  while(fgets(l,100000,fp)){
    vector<string> v0=split(l,":");
    int d=maxguesses-stoi(v0[0]);
    if(d<0||d>maxd||d>=MAXDEPTH)continue;
    int v=stoi(v0[3]);
    list vi1,vi2;
    vector<string> v1=split(v0[1]," "),v2=split(v0[2]," ");
    for(string &s:v1)vi1.push_back(stoi(s));
    for(string &s:v2)vi2.push_back(stoi(s));
    ret[d][list2(vi1,vi2)]=v;
  }
  fclose(fp);
}

void loadcachefromdir(string dir){
  printf("Loading cache from directory \"%s\"...",dir.c_str());fflush(stdout);
  readmap(dir+"/exactcache",opt,maxguesses-minoptcacheremdepth);
  readmap(dir+"/lboundcache",lbound,maxguesses-minlboundcacheremdepth);
  printf("...done\n");
}

void writemap(map<list2,int>*m,string fn){
  int d;
  if(!outdir)return;
  string path=outdir+("/"+fn);
  FILE*fp=fopen(path.c_str(),"w");assert(fp);
  for(d=0;d<=MAXDEPTH;d++){
    for(auto &pair:m[d]){
      fprintf(fp,"%d :",maxguesses-d);
      for(int t:pair.first.first)fprintf(fp," %d",t);
      fprintf(fp," :");
      for(int t:pair.first.second)fprintf(fp," %d",t);
      fprintf(fp," : %d\n",pair.second);
    }
  }
  fclose(fp);
}

void savecache(){
  writemap(opt,"exactcache");
  writemap(lbound,"lboundcache");
}

int keysize(list2&key){
  int x=key.first.size(),y=key.second.size();
  int a=(x==0?0:(x<5?2:(x+11)/8));
  int b=(y==0?0:(y<5?2:(y+11)/8));
  return 16*(a+b)+92;
}

int readoptcache(int depth,list&oktestwords,list&hwsubset){
  if(maxguesses-depth>=minoptcacheremdepth){
    map<list2,int>::iterator it;
    it=opt[depth].find(list2(hardmode?oktestwords:emptylist,hwsubset));
    if(it!=opt[depth].end()){
      cachereads[depth]++;
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
    it=lbound[depth].find(list2(hardmode?oktestwords:emptylist,hwsubset));
    if(it!=lbound[depth].end())return it->second;
  }
  return -1;
}

void writeoptcache(int depth,list&oktestwords,list&hwsubset,int v){
  if(maxguesses-depth>=minoptcacheremdepth){
    list2 key=list2(hardmode?oktestwords:emptylist,hwsubset);
    cachesize[depth]+=keysize(key);
    cachewrites[depth]++;
    opt[depth][key]=v;
  }
}

void writelboundcache(int depth,list&oktestwords,list&hwsubset,int v){
  if(v>=infinity/2){writeoptcache(depth,oktestwords,hwsubset,infinity);return;}
  if(maxguesses-depth>=minlboundcacheremdepth){
    list2 key=list2(hardmode?oktestwords:emptylist,hwsubset);
    map<list2,int>::iterator it;
    it=lbound[depth].find(key);
    if(it!=lbound[depth].end()){cachesize[depth]+=keysize(key);it->second=max(it->second,v);} else lbound[depth][key]=v;
  }
}

void prwordlist(list&wl){
  for(int i:wl)printf("%s ",testwords[i].c_str());
  printf("\n");
}

void inithardmodebitvectors(){
  int a,g,i,j,p,s,nt=testwords.size();;
  multiset64.resize(nt,32);
  testwords25bit.resize(nt);
  for(i=0;i<nt;i++){
    uint t=0;
    for(p=0;p<5;p++)t|=(testwords[i][p]-'a')<<(5*p);
    testwords25bit[i]=t;
  }
  for(s=0;s<243;s++){
    int s1=s,u=0;
    uint v=0;
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
      for(p=0;p<5;p++)if((g>>p)&1)mult[testwords[j][p]-'a']++;
      uint64 t=0;
      for(a=0;a<26;a++){assert(mult[a]<4);t|=uint64(mult[a])<<(a*2);}
      multiset64[j][g]=t;
    }
  }
}

// Is j an allowable testword to choose given that word i has scored s?
// i = past test word
// s = score of past test word
// j = candidate future test word we are determining the legality of
int okhard(int i,int s,int j){
  uint M=greenmask25bit[s];
  uint X=testwords25bit[i]&M;
  uint X1=testwords25bit[j]&M;
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
// Output:
//   new reduced set of allowable test words in hard mode
list filter(list&words,int t,int s){
  if(!hardmode)return words;
  list ret;
  // t1 = hypothetical future test word
  for(int t1:words)if(okhard(t,s,t1))ret.push_back(t1);
  return ret;
}

int minoverwords(list&oktestwords,list&hwsubset,int depth,int toplevel,int beta=infinity,int fast=0,int *rbest=0);

int sumoverpartitions(list&oktestwords,list&hwsubset,int depth,int testword,int biggestendgame,int beta){
  int i,k,m,n,s,nh=hwsubset.size();
  list equiv[243];
  tick(2);
  for(int h:hwsubset){
    s=sc[testword][h];
    equiv[s].push_back(h);
  }
  tock(2);
  int betac=min(beta,infinity/2);
  
  int tot=0;
  if(0>=betac)return beta;
  
  int ind[243],lb[243]={0};
  // First loop over the partition finding out very fast (fast=1) information if available
  tick(3);
  for(n=s=0;s<243;s++){
    if(tot>=betac)return beta;
    int sz=equiv[s].size();
    if(sz){
      if(s==242){lb[s]=1;tot+=1;continue;}
      // Don't need to filter here because oktestwords isn't used in fastmode 1
      int o=minoverwords(oktestwords,equiv[s],depth+1,0,beta-tot-sz,1);
      if(o>=0){lb[s]=sz+o;tot+=lb[s];continue;}
      lb[s]=3*sz-1+max(sz-243,0);
      tot+=lb[s];
      ind[n++]=s;
    }
  }
  if(tot>=betac)return beta;
  tock(3);
  
  // Then loop over the partition finding out medium fast (fast=2) information if available
  list filtered[243];

  tick(4);
  for(k=m=0;k<n;k++){
    if(tot>=betac)return beta;
    s=ind[k];
    int sz=equiv[s].size();
    assert(s<242);
    filtered[s]=filter(oktestwords,testword,s);
    if(sz==nh&&filtered[s].size()==oktestwords.size())return beta;
    if(lb[s]==3*sz-1){
      tot-=lb[s];
      int o=minoverwords(filtered[s],equiv[s],depth+1,0,beta-tot-sz,2);
      if(o>=0){int inc=sz+o;assert(depthonly||inc>=lb[s]);lb[s]=inc;tot+=inc;continue;}
      lb[s]=3*sz;
      {int v=readlboundcache(depth+1,filtered[s],equiv[s]);if(v>=0)lb[s]=max(lb[s],sz+v);}
      tot+=lb[s];
    }
    ind[m++]=s;
  }
  if(tot>=betac)return beta;
  n=m;
  
  tock(4);
  // The '<' sort order makes it faster at finding "disproofs" (beta cutoffs) even though larger equivalence classes are more likely to be worse (they are more likely to cutoff)
  int score[243];
  for(i=0;i<n;i++){
    int r=0,s=ind[i];
    for(int h:equiv[s])for(int e:wordnum2endgame[h])if(e==biggestendgame)r++;
    score[s]=1*equiv[s].size()+0*filtered[s].size();
    if(depth<=-1){// Experimented with directing the search towards smaller set of test words, or to bad endgames, but this didn't seem to help
      //printf("%s %6d",decscore(s).c_str(),score[s]);
      score[s]=-100000/score[s]-(1<<r);
      //printf(" %6d\n",score[s]);
    }
  }
  auto cmp=[&score](const int&s0,const int&s1)->bool{return score[s0]<score[s1];};
  //auto cmp=[&equiv](const int&s0,const int&s1)->bool{return equiv[s0].size()<equiv[s1].size();};
  std::sort(ind,ind+n,cmp);

  // Now loop over the remaining partition doing a full search
  tick(10+depth);
  double cpu0=-1e30,cpu1=-1e30;
  if(depth<=prl)cpu0=cpu();
  for(k=0;k<n;k++){
    s=ind[k];
    int sz=equiv[s].size();
    int inc;
    assert(s<242);
    tot-=lb[s];
    //if(filtered[s].size()==0)filtered[s]=filter(oktestwords,testword,s);
    if(depth<=prl){cpu1=cpu();prs(depth*4+2);printf("S%d %s %5lu %5d %8.2f %d/%d\n",depth,decscore(s).c_str(),filtered[s].size(),sz,cpu(),k,n);fflush(stdout);}
    inc=sz+minoverwords(filtered[s],equiv[s],depth+1,0,beta-tot-sz);
    assert(depthonly||inc>=lb[s]);
    lb[s]=inc;
    tot+=inc;
    if(tot>=betac){
      if(depth<=prl){
        double cpu2=cpu();
        prs(depth*4+2);
        printf("C%d %s %5lu %5d %8.2f    used,wasted = %12.4f %12.4f\n",
               depth,decscore(s).c_str(),filtered[s].size(),sz,cpu2,cpu2-cpu1,cpu1-cpu0);
        fflush(stdout);
      }
      if(exhaust){
        // This indirect reasoning only applies for exhaustive search
        int a,i,j,mm[5]={1,3,9,27,81};
        tick(20+depth);
        if(inc>=infinity/2){
          // The reasoning here is, given an allowable set of test words T, and allowable set of hidden words H0 and H1, with H0 contained in H1, eval(T,H0) <= eval(T,H1)
          // The useful case to apply this to is "when a new letter scores 'B', it's at least better than wasting a letter (by reusing a known non-letter)"
          // This occurs quite a bit in long searches, where there is a long tail of useless test words (containing known non-letters) that are dominated by previous words.
          // In hard mode, if a letter scores 'B' then there are no restrictions on it (hard mode doesn't insist on not using it later), so T is the same for H0 and H1 (as required).
          // For example, after amort.BBBBY.tupik.YBBBB (meaning amort scores BBBBY then tupik scores YBBBB),
          // if BBBBY defeats bowat (renders it impossible: eval=infinity), then wrapt will also be defeated by BBBBY with no further calculation.
          // Proof: Let T and H be the sets of testwords and hiddenwords respectively, after amort.BBBBY.tupik.YBBBB. Note that bowat, wrapt are in T.
          //        H0 = {h in H | score(bowat,h)=BBBBY}
          //        H1 = {h in H | score(wrapt,h)=BBBBY}
          //        H0 is contained in H1, because we already know that a, p and r aren't present, and H0 guarantees w isn't present, and H0 and H1 put the same restrictions on t.
          //        The allowable test sets don't change (from T) after either of these words because 'B's don't impose any restrictions, and we already knew about 't' from amort.
          //        So eval(T,H0) <= eval(T,H1).
          for(i=0;i<5;i++)if( (s/mm[i])%3==0 && (equiv[s+mm[i]].size()>0||equiv[s+2*mm[i]].size()>0) ){
            list u=equiv[s];
            u.insert(u.end(),equiv[s+mm[i]].begin(),equiv[s+mm[i]].end());
            u.insert(u.end(),equiv[s+2*mm[i]].begin(),equiv[s+2*mm[i]].end());
            std::sort(u.begin(),u.end());
            writeoptcache(depth+1,filtered[s],u,infinity);
          }
          for(i=0;i<4;i++)if((s/mm[i])%3==0)for(j=i+1;j<5;j++)if((s/mm[j])%3==0){
            int a,b,t=0;
            for(a=0;a<3;a++)for(b=0;b<3;b++)t+=equiv[s+a*mm[i]+b*mm[j]].size();
            if(t>int(equiv[s].size())){
              list u;
              for(a=0;a<3;a++)for(b=0;b<3;b++){
                list &e=equiv[s+a*mm[i]+b*mm[j]];
                u.insert(u.end(),e.begin(),e.end());
              }
              std::sort(u.begin(),u.end());
              writeoptcache(depth+1,filtered[s],u,infinity);
            }
          }
        }
        if(!hardmode){
          // This is similar to above, but in easy mode we can say more because the allowable test set doesn't change. We can even say something that may be useful in average score mode (as opposed to depthonly mode).
          // The basic point is that eval(H0 u H1) >= eval(H0) + eval(H1). That's because it can't hurt to know some extra information (about whether the hidden word is in H0 or H1) which we can choose not to use.
          // The proof is that you can use the optimal strategy for H0 u H1 separately on H0 and on H1.
          // The use case is generating lower bounds like
          //   eval({h in H | score(bowat,h) in *BBBY}) >= eval({h in H | score(bowat,h)=BBBBY}) + eval({h in H | score(bowat,h)=YBBBY}) + eval({h in H | score(bowat,h)=GBBBY})
          for(i=0;i<5;i++){
            int s0=s-((s/mm[i])%3)*mm[i];
            list u=equiv[s0];
            u.insert(u.end(),equiv[s0+mm[i]].begin(),equiv[s0+mm[i]].end());
            u.insert(u.end(),equiv[s0+2*mm[i]].begin(),equiv[s0+2*mm[i]].end());
            std::sort(u.begin(),u.end());
            int v=0;
            for(a=0;a<3;a++)v=min(v+lb[s0+mm[i]*a]-int(equiv[s0+mm[i]*a].size()),infinity);
            assert(v>=0);
            writelboundcache(depth+1,u,u,v);
          }
        }
        tock(20+depth);
      }
      return beta;
    }
  }
  tock(10+depth);
  assert(tot>=0);
  if(tot>=infinity/2)tot=infinity;
  return min(tot,beta);
}

int minoverwords_fixedlist(list&trywordlist,list&oktestwords,list&hwsubset,int depth,int toplevel,int alpha=0,int beta=infinity,int *rbest=0){
  int nh=hwsubset.size(),nt=oktestwords.size(),remdepth=maxguesses-depth;
  vector<UC> endcount(numendgames);
  int e,biggestendgame=-1,mx=0;

  if(rbest)*rbest=-1;
  for(int h:hwsubset)for(int e:wordnum2endgame[h])endcount[e]++;
  for(e=0;e<numendgames;e++)if(endcount[e]>mx){mx=endcount[e];biggestendgame=e;}
  if(depth<=prl){prs(depth*4);printf("Biggest endgame = %d %d\n",biggestendgame,mx);}

  if(biggestendgame>=0&&nt>=remdepth-1&&remdepth>=1&&mx-1>remdepth-1){
    int sum=0;
    tick(30+depth);
    list liveendgame;
    for(int h:hwsubset)for(int e:wordnum2endgame[h])if(e==biggestendgame)liveendgame.push_back(h);
    int mult[6]={0};
    for(int t:oktestwords){
      UC seen[243]={0};
      int n=0;
      for(int h:liveendgame){
        int s=sc[t][h];
        n+=(seen[s]==0);seen[s]=1;
      }
      assert(n>=1&&n<=6);mult[n-1]++;
    }
    int n,r=remdepth-1;
    for(n=5;n>0&&r>0;n--){int r1=min(r,mult[n]);sum+=r1*n;r-=r1;}
    tock(30+depth);
    if(mx>sum+1){
      if(depth<=prl)printf("Endgame cutoff %d %d %d %5d\n",remdepth-1,mx-1,sum,nt);
      writeoptcache(depth,oktestwords,hwsubset,infinity);
      return infinity;
    } else if(depth<=prl)printf("Endgame notcut %d %d %d %5d\n",remdepth-1,mx-1,sum,nt);
  }
  
  int mi=beta,best=-1,exact=0;
  int word,maxw=trywordlist.size();
  double cpu0=cpu();
  double cpu1=cpu0;
  for(word=0;word<maxw;word++){
    int testword=trywordlist[word];
    if(depth<=prl){prs(depth*4);printf("M%d %s %8.2f %d/%d %d %d\n",depth,testwords[testword].c_str(),cpu(),word,maxw,beta,mi);fflush(stdout);}
    int tot=sumoverpartitions(oktestwords,hwsubset,depth,testword,biggestendgame,beta);

    if(toplevel){
      double cpu2=cpu();
      printf("First guess %s %s= %d     %5d / %5d    dCPU = %9.2f   CPU = %9.2f\n",
             testwords[testword].c_str(),tot<beta||tot==infinity?" ":">",tot,word,maxw,cpu2-cpu1,cpu2-cpu0);
      cpu1=cpu2;
      fflush(stdout);
    }
  
    // tot<beta implies all calls to minoverwords() returned an answer < the beta used to call it, which implies they are all exact
    // And if it's exact for one testword, then the final answer has to be exact because either hit a new exact word, or all subsequent words are >= it in score.
    if(tot<beta)exact=1;
    if(tot<mi){
      mi=tot;best=testword;
      if(toplevel<2)beta=mi;
    }
    if(depth<=prl){prs(depth*4);printf("N%d %s %8.2f %d/%d %d %d : %d\n",depth,testwords[testword].c_str(),cpu(),word,maxw,beta,mi,tot);fflush(stdout);}
    if(toplevel<2&&mi<=alpha)break;// alpha is a guaranteed lower bound (not just a number that we don't care how much we are below), so if we cutoff here it is still valid to write mi to cache
    if(depthonly&&toplevel<2&&mi<infinity/2)break;

  }
  if(mi>=infinity/2){mi=infinity;exact=1;}
  if(exact){optstats[nh][0]++;optstats[nh][1]+=mi;}
  if(exact)writeoptcache(depth,oktestwords,hwsubset,mi);
  if(!exact)writelboundcache(depth,oktestwords,hwsubset,mi);
  if(rbest)*rbest=best;
  return mi;
}


// Returns minimum_{s in considered strategies} sum_{h in hiddenwordsubset} (number of guesses strategy s requires for word h)
//      or -1 in fast mode, which means "Can't find a fast answer"
int minoverwords_inner(list&oktestwords,list&hwsubset,int depth,int toplevel,int beta=infinity,int fast=0,int *rbest=0){
  int i,t,nh=hwsubset.size(),remdepth=maxguesses-depth;
  assert(depth<MAXDEPTH);
  totentries++;
  entrystats[depth][0]++;
  if(depth<=prl){
    prs(depth*4);
    printf("E%d %4d",depth,nh);
    for(i=0;i<min(nh,200);i++)printf(" %s",testwords[hwsubset[i]].c_str());
    if(i<nh)printf(" ...\n"); else printf("\n");
    fflush(stdout);
  }
  if(rbest)*rbest=-1;
  if(remdepth<=0)return beta;
  if(2*nh-1>=beta)return beta;
  if(nh==1){if(rbest)*rbest=hwsubset[0];return 1;}
  if(remdepth<=1)return beta;
  if(nh==2){if(rbest)*rbest=hwsubset[0];return 3;}
  entrystats[depth][1]++;
  if(fast==1)return -1;
  if(!rbest&&toplevel<2){int v=readoptcache(depth,oktestwords,hwsubset);if(v>=0)return v;}
  entrystats[depth][2]++;
  tick(0);tock(0);// calibration
  if(totentries>=nextcheck){
    int d;
    int64 n=0;
    for(d=0;d<=MAXDEPTH;d++)n+=cachesize[d];
    //if(prl>=0)printf("%8.2f Est cache size %.3f GB\n",cpu(),n/1e9);
    if(n/1e9>=cachememlimit){
      int64 nmax=int64(0.9*cachememlimit*1e9);
      for(d=MAXDEPTH;d>=0;d--){
        n-=cachesize[d];
        cachesize[d]=0;
        opt[d].clear();
        lbound[d].clear();
        if(n<=nmax)break;
      }
      if(prl>=0)printf("%8.2f Clearing caches at depths >=%d\n",cpu(),d);
    }
    if(checkpointinterval>=0&&cpu()>=nextcheckpoint){
      writeoptstats();
      savecache();
      nextcheckpoint+=checkpointinterval;
    }
    nextcheck+=checkinterval;
  }
  
  int nt=oktestwords.size();
  int thr;
  vector<uint64> s2a(nt);

  int count[243];
  tick(5);
  // Check for perfect test word, which would mean we don't need to consider others
  int good=-1;
  for(int t:hwsubset){
    memset(count,0,sizeof(count));
    int bad=0;
    for(int h:hwsubset){
      int c=(++count[sc[t][h]]);
      bad+=(c>=2);
    }
    if(bad==0){
      writeoptcache(depth,oktestwords,hwsubset,2*nh-1);
      if(rbest)*rbest=t;
      return 2*nh-1;
    }
    if(bad==1)good=t;
  }
  if(good>=0&&remdepth>=3){
    writeoptcache(depth,oktestwords,hwsubset,2*nh);
    if(rbest)*rbest=good;
    return 2*nh;
  }
  tock(5);
  if(fast==2)return -1;
  
  tick(1);
  int lb1=infinity;
  good=-1;
  for(i=0;i<nt;i++){
    t=oktestwords[i];
    memset(count,0,sizeof(count));
    int s2=0,lb=nh,upto2=1;
    for(int h:hwsubset){
      int &c=count[sc[t][h]];
      c++;
      lb+=2-(c==1);// Assumes remdepth>=3
      if(c>2)upto2=0;
      s2+=2*c-1;
    }
    lb-=count[242];
    if(lb<lb1)lb1=lb;
    if(lb==2*nh+1&&upto2)good=t;// Try this later, after eliminating the 2*nh possibilities
    // Check for a split into singletons using a word that couldn't be the answer, which means we can achieve 2*nh within remdepth 2
    if(count[242]==0&&s2==nh){
      writeoptcache(depth,oktestwords,hwsubset,2*nh);
      if(rbest)*rbest=t;
      return 2*nh;
    }
    s2a[i]=int64(s2mult*s2+nh*lb)<<32|t;
  }
  tock(1);
  
  // Having not found a testword that splits into singletons, we must require at least 3 guesses in worst case.
  if(remdepth<=2){
    writeoptcache(depth,oktestwords,hwsubset,infinity);
    return infinity;
  }
  // Can't early exit like this for higher scores than 2*nh+1, because 2*nh+1 can arise from a partition 3, 1, 1, ..., if 3 is optimal
  if(good>=0){
    writeoptcache(depth,oktestwords,hwsubset,2*nh+1);
    if(rbest)*rbest=good;
    return 2*nh+1;
  }
  if(lb1>=beta)return beta;
  if(toplevel&&n0th>0)thr=n0th; else thr=nth;
  if(depthonly||depth<=2)std::sort(s2a.begin(),s2a.end()); else if(thr-1<nt)std::nth_element(&s2a[0],&s2a[thr-1],&s2a[nt]);

  list trywordlist;
  int word,maxw=min(thr,nt);
  for(word=0;word<maxw;word++){
    int testword=s2a[word]&((1ULL<<32)-1);
    trywordlist.push_back(testword);
  }
  return minoverwords_fixedlist(trywordlist,oktestwords,hwsubset,depth,toplevel,lb1,beta,rbest);
}

int minoverwords(list&oktestwords,list&hwsubset,int depth,int toplevel,int beta,int fast,int *rbest){
  int o=minoverwords_inner(oktestwords,hwsubset,depth,toplevel,beta,fast,rbest);
  if(o==-1)return -1;
  return min(o,beta);
}

int toplevel_minoverwords(int beta,int*rbest,state*rstate=0){
  vector<string> initial=split(topword?topword:"",".,");
  int i,n=initial.size(),testword=-1;
  list oktestwords=alltest,hwsubset=allhidden;
  for(i=0;i<n;i+=2){
    testword=-1;
    std::transform(initial[i].begin(), initial[i].end(), initial[i].begin(), [](unsigned char c){ return std::tolower(c); });
    for(int t:oktestwords)if(testwords[t]==initial[i]){testword=t;break;}
    if(testword==-1){fprintf(stderr,"Initial word %s is illegal\n",initial[i].c_str());exit(1);}
    if(i+1==n)break;
    // Reduce oktestwords and hwsubset, given that the word initial[i] scored initial[i+1]
    int s=encscore(initial[i+1]);
    oktestwords=filter(oktestwords,testword,s);
    list hwnew;
    for(int h:hwsubset)if(sc[testword][h]==s)hwnew.push_back(h);
    hwsubset=hwnew;
    if(hwsubset.size()==0){fprintf(stderr,"Impossible initial scoring: %s\n",topword);exit(1);}
  }
  writewordlist(hwsubset,"hiddenwords_afterinitial");
  writewordlist(oktestwords,"testwords_afterinitial");

  int depth=i/2;
  if(rstate){rstate->depth=depth;rstate->oktestwords=oktestwords;rstate->hwsubset=hwsubset;}
  
  if(i==n&&!toplist)return minoverwords(oktestwords,hwsubset,depth,1+showtop,beta,0,rbest);
  
  list trywordlist;
  if(!toplist){
    trywordlist.push_back(testword);
  }else{
    int start=0,step=1;
    vector<string> tlf=split(toplist,",");
    vector<string> fwl=load(tlf[0].c_str());
    if(tlf.size()>=2)start=std::stoi(tlf[1]);
    if(tlf.size()>=3)step=std::stoi(tlf[2]);
    for(int j=start;j>=0&&j<int(fwl.size());j+=step){
      for(int t:oktestwords)if(fwl[j]==testwords[t])trywordlist.push_back(t);
    }
  }
  return minoverwords_fixedlist(trywordlist,oktestwords,hwsubset,depth,1+showtop,0,beta,rbest);
  
}

int printtree(list oktestwords,list&hwsubset,int depth,FILE*tfp){
  int i,j,o,s,best;
  state state;

  if(depth==0){
    o=toplevel_minoverwords(infinity,&best,&state);
    depth=state.depth;
    oktestwords=state.oktestwords;
    hwsubset=state.hwsubset;
    for(j=0;j<depth*13;j++)fprintf(tfp," ");
  } else o=minoverwords(oktestwords,hwsubset,depth,0,infinity,0,&best);
  if(best==-1){
    fprintf(tfp,"IMPOSSIBLE\n");
    return o;
  }
  fprintf(tfp,"%s ",testwords[best].c_str());
  
  list equiv[243];
  for(int h:hwsubset){
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

// hiddenwords has to be an initial segment of testwords
void orderwordlists(){
  std::sort(hiddenwords.begin(),hiddenwords.end());
  vector<string> testonly;
  for(string&s:testwords){
    if(!std::binary_search(hiddenwords.begin(),hiddenwords.end(),s))testonly.push_back(s);
  }
  std::sort(testonly.begin(),testonly.end());
  testwords=hiddenwords;
  testwords.insert(testwords.end(),testonly.begin(),testonly.end());
}

void initendgames(){
  int e,i,j,nh=hiddenwords.size();
  map<string,uint> wcount;// Map from wildcarded string, e.g. ".arks", to number of occurrences
  map<string,int> w2e;    // Map from wildcarded string, e.g. ".arks", to endgame number
  
  for(string &s:hiddenwords){
    for(j=0;j<5;j++){
      string t=s.substr(0,j)+"."+s.substr(j+1,5-(j+1));
      if(wcount.count(t)==0)wcount[t]=0;
      wcount[t]++;
    }
  }
  
  wordnum2endgame.resize(nh);
  numendgames=0;
  for(i=0;i<nh;i++){
    string s=hiddenwords[i];
    for(j=0;j<5;j++){
      string t=s.substr(0,j)+"."+s.substr(j+1,5-(j+1));
      if(wcount[t]>=minendgamecount){
        if(w2e.count(t)==0)w2e[t]=numendgames++;
        wordnum2endgame[i].push_back(w2e[t]);
      }
    }
  }

  vector<list> endgame2wordlist(numendgames);
  for(i=0;i<nh;i++)for(int e:wordnum2endgame[i])endgame2wordlist[e].push_back(i);

  if(outdir){
    FILE*fp=fopen((string(outdir)+"/word2endgame").c_str(),"w");assert(fp);
    for(i=0;i<nh;i++){
      if(wordnum2endgame[i].size()){
        fprintf(fp,"%s",testwords[i].c_str());
        for(int e:wordnum2endgame[i])fprintf(fp," %d",e);
        fprintf(fp,"\n");
      }
    }
    fclose(fp);

    fp=fopen((string(outdir)+"/endgame2words").c_str(),"w");assert(fp);
    for(e=0;e<numendgames;e++){
      fprintf(fp,"%5d %2lu",e,endgame2wordlist[e].size());
      for(int h:endgame2wordlist[e])fprintf(fp," %s",testwords[h].c_str());
      fprintf(fp,"\n");
    }
    fclose(fp);
  }
}

void initstuff(const char*loadcache){
  printf("Initialising...");fflush(stdout);
  hiddenwords=load(wordlist_hidden_name);
  testwords=load(wordlist_all_name);
  orderwordlists();
  optstats.resize(hiddenwords.size()+1,2);
  if(outdir)mkdir(outdir,0777);
  if(loadcache)loadcachefromdir(loadcache);
  int i,j,nt=testwords.size(),nh=hiddenwords.size();
  sc.resize(nt,nh);
  for(i=0;i<nt;i++)for(j=0;j<nh;j++)sc[i][j]=score(testwords[i],hiddenwords[j]);
  inithardmodebitvectors();
  alltest.resize(nt);for(j=0;j<nt;j++)alltest[j]=j;
  allhidden.resize(nh);for(j=0;j<nh;j++)allhidden[j]=j;
  writewordlist(alltest,"testwords");
  writewordlist(allhidden,"hiddenwords");
  maxguesses=min(maxguesses,MAXDEPTH);
  for(i=0;i<243;i++)humanorder[i]=i;
  auto cmp=[](const int&i0,const int&i1)->bool{return decscore(i0)<decscore(i1);};
  std::sort(humanorder,humanorder+243,cmp);
  initendgames();
  printf("...done\n");
}

int main(int ac,char**av){
  printf("Commit %s\n",COMMITDESC);
  int beta=infinity;
  const char*treefn=0,*loadcache=0;

  while(1)switch(getopt(ac,av,"a:b:c:C:de:Hh:r:R:n:N:g:l:p:st:M:Tw:x:z:")){
    case 'a': wordlist_all_name=strdup(optarg);break;
    case 'b': beta=atoi(optarg);break;
    case 'c': cachememlimit=atof(optarg);break;
    case 'C': checkpointinterval=atof(optarg);break;
    case 'd': depthonly=1;break;
    case 'e': minendgamecount=atoi(optarg);break;
    case 'H': hardmode=1;break;
    case 'h': wordlist_hidden_name=strdup(optarg);break;
    case 'l': loadcache=strdup(optarg);break;
    case 'n': nth=atoi(optarg);break;
    case 'N': n0th=atoi(optarg);break;
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
    case 'z': prl=atoi(optarg);break;
    case -1: goto ew0;
    default: goto err0;
  }
 ew0:;
  if(optind<ac){
  err0:
    fprintf(stderr,"Options: a=wordlist_all_name, b=beta, c=approx cache memory limit in GB, C=cache checkpoint interval in seconds (default=no checkpointing), d enables depth-only mode, e=minendgamecount, H enables hard mode, h=wordlist_hidden_name, n=nth, N=nth at top level, g=max guesses, p=print tree filename, r,R = things, s enables showtop, t=toplist filename[,start[,step]], w=topword, T enables timings, x=outdir\n");
    exit(1);
  }

  initstuff(loadcache);
  if(nth==-1)nth=testwords.size();
  exhaust=(nth>=int(testwords.size()));

  printf("Mode: %s\n",hardmode?"Hard":"Easy");
  printf("nth = %d\n",nth);
  printf("n0th = %d\n",n0th);
  printf("Exhaustive search = %d\n",exhaust);
  printf("maxguesses = %d\n",maxguesses);
  printf("beta = %d\n",beta);
  printf("showtop = %d\n",showtop);
  printf("top-level list = %s\n",toplist?toplist:"(not given)");
  printf("top-level word = %s\n",topword?topword:"(not given)");
  if(checkpointinterval<0)printf("Cache checkpointing off\n"); else printf("Cache checkpoint interval = %gs\n",checkpointinterval);
  printf("s2mult = %d\n",s2mult);
  printf("depthonly = %d\n",depthonly);
  printf("Test wordlist filename = %s, size = %lu\n",wordlist_all_name,testwords.size());
  printf("Hidden wordlist filename = %s, size = %lu\n",wordlist_hidden_name,hiddenwords.size());
  printf("tree filename = %s\n",treefn?treefn:"(not given)");
  printf("min{opt,lbound}cacheremdepths = %d %d\n",minoptcacheremdepth,minlboundcacheremdepth);
  printf("minendgamecount = %d\n",minendgamecount);
  printf("Number of endgames = %d\n",numendgames);
  printf("Cache memory limit ~= %.1f GB\n",cachememlimit);
  fflush(stdout);
  double cpu0=cpu();
  int i,o,nh;
  if(treefn){
    FILE*tfp=fopen(treefn,"w");assert(tfp);
    list test0=alltest,hidden0=allhidden;
    o=printtree(test0,hidden0,0,tfp);
    fclose(tfp);
    printf("Written tree to file \"%s\"\n",treefn);
    nh=hidden0.size();
  }else{
    int best;
    state state;
    o=toplevel_minoverwords(beta,&best,&state);
    printf("Best first guess = %s\n",best>=0?testwords[best].c_str():"no-legal-guess");
    nh=state.hwsubset.size();
  }
  printf("Best first guess score %s= %d\n",depthonly&&o<infinity?"<":"",o);
  if(!depthonly)printf("Average guesses reqd using best first guess = %.4f\n",o/double(nh));
  double cpu1=cpu()-cpu0;
  printf("Time taken = %.2fs\n",cpu1);
  for(i=0;i<=maxguesses;i++)if(cachereads[i]||entrystats[i][0])printf("Depth %2d: Entries = %12lld %12lld %12lld    Cache writes reads misses = %12lld %12lld %12lld\n",i,entrystats[i][0],entrystats[i][1],entrystats[i][2],cachewrites[i],cachereads[i],cachemiss[i]);
  writeoptstats();
  if(checkpointinterval>=0)savecache();
  prtim();
}
