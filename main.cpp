#include <iostream>
#include <fstream>
#include <cstring>
#include <vector>
#include <cmath>
#include <algorithm>
#include <functional>

using namespace std;

typedef struct _decTable {
	float* valAttributes;
	string valDecision;
} TdecisionTable;
vector<TdecisionTable> decisionTable;
vector<string> nameAttributes;
string nameDecision;
int numOfCases, numOfAttributes;

typedef struct _relSet {
	int* index;
	int numSubset;
} TresultSet;
TresultSet dStar;
TresultSet resultSet;

typedef struct _cutpts {
	float val;
	int index;
	bool valid;
} TcutPoints;
vector<TcutPoints> cutPoints;

typedef struct _cutsec {
	float *Upper;
	float *Lower;
	int numSection;
} TcutSection;
TcutSection *cutSection;

int **solveTable;

bool read_input(char* inputFile,int &numOfCases, int &numOfAttributes) {
	ifstream fin;
	numOfCases=0;
	numOfAttributes=0;
	int idxattr=0;
	string SName;
	char t='~';
	int indicator=0;//1 2
	string comline;
	fin.open(inputFile);
	TdecisionTable TCase;
	TCase.valAttributes=NULL;
	TCase.valDecision="";
	if (fin.is_open()) { //
		cout<<endl<<"Read "<<inputFile<<" successfully!"<<endl;
		while (fin.good()) {
			if (t=='!') {getline(fin,comline);fin>>t;} 
			else if ((t=='<')&&(indicator==0)) {
				indicator=1;
				fin>>t;
			} else if ((t=='a')&&(indicator==1)) {
				numOfAttributes++;
				fin>>t;
			} else if ((t=='[')&&(indicator==1)) {
				indicator=2;
				for (int i=0;i<numOfAttributes;i++) {
					fin>>SName;
					nameAttributes.push_back(SName);
				}
				fin>>nameDecision;
				fin>>t;
			} else if (((t>=48)&&(t<=57)||(t=='-'))&&(indicator==2)&&(idxattr<numOfAttributes)) {
				fin.putback(t);
				if (idxattr==0) {
					TCase.valAttributes=new float[numOfAttributes];
					fin>>TCase.valAttributes[idxattr];
					idxattr++;
				} else {
					fin>>TCase.valAttributes[idxattr];
					idxattr++;
				}
				fin>>t;
			} else if ((indicator==2)&&(idxattr==numOfAttributes)&&(t!=' ')) {
				fin.putback(t);
				fin>>TCase.valDecision;
				decisionTable.push_back(TCase);
				TCase.valDecision="";
				TCase.valAttributes=NULL;
				idxattr=0;
				fin>>t;
			} else fin>>t;
		}
		fin.close();
	} else {
		cerr<<"Cannot open input file:"<<inputFile<<endl;
		return false;
	}
	numOfCases=decisionTable.size();
	return true;
}

void ComputedStar(int &numOfCases) {
	dStar.numSubset=0;
	dStar.index=new int[numOfCases];
	memset(dStar.index,0,sizeof(dStar.index));
	vector<string> searchT;
	vector<string>::iterator it;
	for (int i=0;i<numOfCases;i++) {
		it=find(searchT.begin(),searchT.end(),decisionTable[i].valDecision);
		if (it==searchT.end()) {
			searchT.push_back(decisionTable[i].valDecision);
			dStar.index[i]=searchT.end()-searchT.begin()-1;
			dStar.numSubset++;
		} else dStar.index[i]=it-searchT.begin();
	}
	vector<string>().swap(searchT);
}

void BuildSolveTable(int &numOfCases, int &numOfAttributes) {
	solveTable=new int*[numOfAttributes];
	float *temp=new float[numOfCases];
	for (int i=0;i<numOfAttributes;i++) {
		solveTable[i]=new int[numOfCases];	
		for (int j=0;j<numOfCases;j++) {
			solveTable[i][j]=j;
			temp[j]=decisionTable[j].valAttributes[i];
		}
		for (int m=0;m<numOfCases;m++)
			for (int n=m+1;n<numOfCases;n++)
				if (temp[m]>temp[n]) {
					int t=solveTable[i][m];
					solveTable[i][m]=solveTable[i][n];
					solveTable[i][n]=t;
					float tt=temp[m];
					temp[m]=temp[n];
					temp[n]=tt;
				}
	}
	delete [] temp;
}

float ComputeLog(int a, int b) { //a/b*l2(a/b)
	float v;
	if (a==b) return 0;
	v=((float)a)/((float)b);
	return -v*log(v)/log(2);	
}

float ComputeInnerE(vector<int> &subsection,int head,int tail) {
	vector<string> searchT;
	vector<int> t;
	vector<string>::iterator it;
	float result=0;
	int n=tail-head+1;
	if (n==1) return 0;
	for (int i=head;i<=tail;i++) {
		it=find(searchT.begin(),searchT.end(),decisionTable[subsection[i]].valDecision);
		if (it==searchT.end()) {
			searchT.push_back(decisionTable[subsection[i]].valDecision);
			t.push_back(1);
		} else t[it-searchT.begin()]++;
	}
	int nt=t.size();
	for (int i=0;i<nt;i++) {
		result+=ComputeLog(t[i],n);
	}
	vector<string>().swap(searchT);
	vector<int>().swap(t);
	return result;
}

float ComputeE(int attr, int sub, int &numOfCases) {
	float E=0;
	int head,tail,j;
	head=0;
	tail=0;
	vector<int> temp;
	for (int i=0;i<numOfCases;i++)
		if (resultSet.index[solveTable[attr][i]]==sub) temp.push_back(solveTable[attr][i]);
	int n=temp.size();
	for (int i=0;i<n-1;i++) 
		if(decisionTable[temp[i]].valAttributes[attr]!=decisionTable[temp[i+1]].valAttributes[attr]) {
			tail=i;
			E+=(float)(tail-head+1)/(float)n*ComputeInnerE(temp,head,tail);
			head=tail+1;
		}
	E+=(float)(n-head)/(float)n*ComputeInnerE(temp,head,n-1);
	vector<int>().swap(temp);
	return E;	
}

float ComputeBestCutPoints(int attr, int sub, int &numOfCases) {
	float cutPoint=0,_cutPoint;
	float E=2;//maximum entrop is 1;
	float t=0;
	vector<int> temp;
	for (int i=0;i<numOfCases;i++)
		if (resultSet.index[solveTable[attr][i]]==sub) temp.push_back(solveTable[attr][i]);
	int n=temp.size();
	
	for (int i=0;i<n-1;i++) {
			if (decisionTable[temp[i]].valAttributes[attr]!=decisionTable[temp[i+1]].valAttributes[attr]) {
				_cutPoint=(decisionTable[temp[i]].valAttributes[attr]+decisionTable[temp[i+1]].valAttributes[attr])/2;
				t=(float)(i+1)/(float)n*ComputeInnerE(temp,0,i);
				t+=(float)(n-1-i)/(float)n*ComputeInnerE(temp,i+1,n-1);
				if (t<E) {E=t;cutPoint=_cutPoint;}
			}
	}
	return cutPoint;
}

bool MultSubSet(TresultSet &a,TresultSet &b, int suba, int subb, int &numOfCases, vector<int>& result) {
	vector<int> va,vb;
	vector<int>::iterator it;
	vector<int>().swap(result);
	for (int i=0;i<numOfCases;i++) {
		if (a.index[i]==suba) va.push_back(i);
		if (b.index[i]==subb) vb.push_back(i);
	}
	int n=va.size();
	for (int i=0;i<n;i++) {
		it=find(vb.begin(),vb.end(),va[i]);
		if (it!=vb.end()) result.push_back(va[i]);
	}
	
	if (result.size()==va.size()) {
		vector<int>().swap(va);
		vector<int>().swap(vb);
		return true;
	}
	else {
		vector<int>().swap(va);
		vector<int>().swap(vb);
		return false;
	}
}

bool CheckBelong(TresultSet &a,TresultSet &b) {
	vector<int> result;
	for (int i=0;i<a.numSubset;i++) {
		bool id=false;
		for (int j=0;j<b.numSubset;j++) {
			if (MultSubSet(a,b,i,j,numOfCases,result)) 
				{id=true; j=b.numSubset;}
		}
		if (!id) 
			{vector<int>().swap(result);return false;}
	}
	vector<int>().swap(result);
	return true;
}

bool CheckSubBelong(TresultSet &a,int suba, TresultSet &b) {
	vector<int> result;
	for (int j=0;j<b.numSubset;j++) {
		if (MultSubSet(a,b,suba,j,numOfCases,result)) 
			{vector<int>().swap(result);return true;}
	}
	vector<int>().swap(result);
	return false;
}

void BuildAttrSet(int attr, int &numOfCases, TresultSet &result) {
	vector<float> cutPointAttr;
	result.index=new int[numOfCases];

	int n=cutPoints.size();
	for (int i=0;i<n;i++)
		if ((cutPoints[i].valid)&&(cutPoints[i].index==attr)) cutPointAttr.push_back(cutPoints[i].val);
	n=cutPointAttr.size();
	if (n==0) {
		result.numSubset=1;
		for (int i=0;i<numOfCases;i++)
			result.index[i]=0;
	} else {
		sort(cutPointAttr.begin(),cutPointAttr.end());
		result.numSubset=1;	
		int count=0;
		for (int i=0;i<numOfCases;i++) {
			if (decisionTable[solveTable[attr][i]].valAttributes[attr]<cutPointAttr[count]) {
				result.index[solveTable[attr][i]]=count;
			} else if (count==n){
				result.index[solveTable[attr][i]]=count;
			} else {
				count++;
				result.numSubset++;
				result.index[solveTable[attr][i]]=count;
			}
		}
	}
	vector<float>().swap(cutPointAttr);
}

void BuildResultSet(int &numOfCases,int &numOfAttributes,TresultSet &resultSet) {
	TresultSet resultAttr;
	TresultSet _result;
	vector<int> temp;
	bool id;

	_result.numSubset=1;
	_result.index=new int[numOfCases];
	for (int i=0;i<numOfCases;i++)
		_result.index[i]=0;

	for (int i=0;i<numOfAttributes;i++) {
		BuildAttrSet(i,numOfCases,resultAttr);
		int idx=0;
		resultSet.index=new int[numOfCases];
		for (int m=0;m<_result.numSubset;m++) {
			for (int n=0;n<resultAttr.numSubset;n++) {
				id=MultSubSet(_result,resultAttr,m,n,numOfCases,temp);
				int tt=temp.size();
				if (tt!=0) {
					for (int p=0;p<tt;p++)
						resultSet.index[temp[p]]=idx;
					idx++;
					resultSet.numSubset=idx;
					vector<int>().swap(temp);
				}
			}
		}
		delete [] _result.index;
		_result.index=resultSet.index;
		_result.numSubset=resultSet.numSubset;
		delete [] resultAttr.index;
		resultAttr.index=NULL;
		resultSet.index=NULL;
	}
	resultSet.index=_result.index;
	_result.index=NULL;
	resultSet.numSubset=_result.numSubset;
}

void RemoveCut() {
	int n=cutPoints.size();
	cout<<"Begin to remove cutpoints."<<endl;
	for (int i=0;i<n;i++) {
		if (cutPoints[i].valid) {
			cutPoints[i].valid=false;
			delete [] resultSet.index;
			BuildResultSet(numOfCases,numOfAttributes,resultSet);
			if (CheckBelong(resultSet,dStar)) {		
				cout<<"Cutpoint "<<cutPoints[i].val<<" of "<<nameAttributes[cutPoints[i].index]<<" has been removed."<<endl;
				i=0;
			} else
				cutPoints[i].valid=true;
		}
	}
}

void PrintInf(char *fileName,int &numOfAttributes, int &numOfCases) {
	char outFileName[128];
	int i=0;
	while (fileName[i]!='.') {
		outFileName[i]=fileName[i];
		i++;
	}
	outFileName[i]='.'; i++;
	outFileName[i]='i'; i++;
	outFileName[i]='n'; i++;
	outFileName[i]='f'; i++;
	outFileName[i]='\0';
	ofstream fout;
	vector<float> cutPointAttr;
	int n=cutPoints.size();
	cutSection=new TcutSection[numOfAttributes];
	for (int attr=0;attr<numOfAttributes;attr++) {
		cutPointAttr.push_back(decisionTable[solveTable[attr][0]].valAttributes[attr]);
		for (int i=0;i<n;i++)
			if ((cutPoints[i].valid)&&(cutPoints[i].index==attr)) cutPointAttr.push_back(cutPoints[i].val);
		cutPointAttr.push_back(decisionTable[solveTable[attr][numOfCases-1]].valAttributes[attr]);
		int nn=cutPointAttr.size();
		sort(cutPointAttr.begin(),cutPointAttr.end());
		cutSection[attr].Upper=new float[nn-1];
		cutSection[attr].Lower=new float[nn-1];
		cutSection[attr].numSection=nn-1;
		for (int i=0;i<nn-1;i++) {
			cutSection[attr].Lower[i]=cutPointAttr[i];
			cutSection[attr].Upper[i]=cutPointAttr[i+1];
		}
		vector<float>().swap(cutPointAttr);
	}
	

	fout.open(outFileName);	
	for (int i=0;i<numOfAttributes;i++) {
		fout<<nameAttributes[i]<<": ";
		for (int j=0;j<cutSection[i].numSection;j++) 
			fout<<cutSection[i].Lower[j]<<".."<<cutSection[i].Upper[j]<<"   ";
		fout<<endl;
	}
	fout.close();
	cout<<outFileName<<" has been created!"<<endl;
}

int FindSection(int &numOfAttributes,int attr,int cases){
	for (int i=0;i<cutSection[attr].numSection;i++) {
		if ((decisionTable[cases].valAttributes[attr]>=cutSection[attr].Lower[i])&&
			(decisionTable[cases].valAttributes[attr]<=cutSection[attr].Upper[i]))
			return i;
	}
}

void PrintDisc(char *fileName, int &numOfAttrbutes, int &numOfCases) {
	char outFileName[128];
	int i=0;
	while (fileName[i]!='.') {
		outFileName[i]=fileName[i];
		i++;
	}
	outFileName[i]='.'; i++;
	outFileName[i]='d'; i++;
	outFileName[i]='i'; i++;
	outFileName[i]='s'; i++;
	outFileName[i]='c'; i++;
	outFileName[i]='\0';
	ofstream fout;
	fout.open(outFileName);
	fout<<"< ";
	for (int i=0;i<numOfAttributes;i++)
		fout<<"a ";
	fout<<"d >"<<endl;
	fout<<"[ ";
	for (int i=0;i<numOfAttributes;i++)
		fout<<nameAttributes[i]<<" ";
	fout<<nameDecision<<" ]"<<endl;
	for (int i=0;i<numOfCases;i++) {
		for (int j=0;j<numOfAttributes;j++) {
			int num=FindSection(numOfAttributes,j,i);
			fout<<cutSection[j].Lower[num]<<".."<<cutSection[j].Upper[num]<<" ";
		}
		fout<<decisionTable[i].valDecision<<endl;
	}
	fout.close();
	cout<<outFileName<<" has been created!"<<endl;
}

int main(void) {
string y;
char fileName[128];
TcutPoints Tcut;

while (true) {
	cout<<"Would you like to start the program? (y/n):";
	cin>>y;
	if (y[0]=='y') {
		cout<<"Please tell me the name of the input data file:";
		cin>>fileName;
		if (read_input(fileName,numOfCases,numOfAttributes)) {
			if (numOfCases*numOfAttributes>=1000) {
				cout<<"Input data size is a little bigger."<<endl;
				cout<<"Please be patient..It may take some time to finish.:)"<<endl;
			}
			ComputedStar(numOfCases);
			BuildSolveTable(numOfCases,numOfAttributes);
			resultSet.index=new int[numOfCases];
			resultSet.numSubset=1;
			for (int i=0;i<numOfCases;i++)
				resultSet.index[i]=0;
			int sub=0;
			int step=1;
			while (true) {
				float TE;
				float E=2;
				float Att;
				float bestCut;
				for (int i=0;i<numOfAttributes;i++) {
					TE=ComputeE(i,sub,numOfCases);
					if (E>TE) {E=TE;Att=i;}
				}
				Tcut.val=ComputeBestCutPoints(Att,sub,numOfCases);
				Tcut.index=Att;
				Tcut.valid=true;
				cutPoints.push_back(Tcut);
				cout<<"Iteration:"<<step<<"	";
				step++;
				cout<<"Find best cutpoint "<<Tcut.val<<" for "<<nameAttributes[Tcut.index]<<endl;
				delete [] resultSet.index;
				BuildResultSet(numOfCases,numOfAttributes,resultSet);
				if (CheckBelong(resultSet,dStar)) {
					RemoveCut();
					PrintInf(fileName,numOfAttributes,numOfCases); 
					PrintDisc(fileName,numOfAttributes,numOfCases);
					cout<<"Finished!"<<endl;
					break;
				} else {
					for (int i=0;i<resultSet.numSubset;i++)
						if (!CheckSubBelong(resultSet,i,dStar))
							{sub=i;i=resultSet.numSubset;}
				}
			}
			vector<string>().swap(nameAttributes);
			for (int i=0;i<numOfAttributes;i++)
				delete [] solveTable[i];
			delete [] solveTable;
			vector<TcutPoints>().swap(cutPoints);
			int dt=numOfCases;
			for (int i=0;i<dt;i++)
				delete [] decisionTable[i].valAttributes;
			for (int i=0;i<numOfAttributes;i++) {
				delete [] cutSection[i].Upper;
				delete [] cutSection[i].Lower;
			}
			delete [] cutSection;
			vector<TdecisionTable>().swap(decisionTable);
			delete [] dStar.index;
			delete [] resultSet.index;
		}
	} else if (y[0]=='n') break;
}//release vector
cout<<endl<<"Program finished."<<endl;
}
