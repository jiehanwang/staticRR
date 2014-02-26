// staticRR.cpp : Defines the entry point for the console application.
//
#include "stdafx.h"
#include<iostream>
#include<fstream>
#include<vector>
#include<algorithm>
#include<string>
// #include<cv.h>
// #include<highgui.h>
#include <opencv2\opencv.hpp>
#include <time.h>
#include<atlstr.h>
#include<cmath>
#include <direct.h>
using namespace std;
using namespace cv;
#define SIZE 64
#define LRB 3    //Left, right, both
#define FusedLRB 1
#define MarryThre 0.5
#define PairSumBonus 0.0375   //0.0375 Bonus for pair number.
#define WordNum 370 //1000//370
// #define NotCombinePenalty 1  //0.95 Penalty not combined postures by multiply it by 0.5.
// #define CombineBonus 1.0        //1.0

//#define HOG_dimension 1764//dimension of HOG feature
struct Std
{
	IplImage * pic_route;//Pointer to the key frame sequence.
	double std_distance; //Distance to the mean image.
	Std(IplImage * choose_route)
	{
		pic_route=choose_route;
	}
};
struct Rank//For sorting at the final step
{
	int no;//Original index
	double distance;//Distance from gesture i to j
	Rank(int a,double b)
	{
		no=a;
		distance=b;
	}
};
struct Pair
{
	int man;
	int woman;
	double love;
	int married;  //1: married. 0: unmarried. 2: may be
};
vector<Rank>     Last_temp;
Rank                  *p;
CString              Add="\\*.*";
ifstream            infile;               //Define input file object: infile
ifstream            infileMask;               //Define input file object: infile
ofstream           outfile;              //Define output file object: outfile
ofstream           firstRankOutfile;
Std                    *p_std;
vector<Std>      choose_pic;           //Store the best picture.
int                     _count=0;             //Value of C(n,m)
int                     c_choice,c_total;     //分别代表选择的个数和总的个数
int                     _temp[15];
int                     combination[6440][15];//Store all the combination result.
double*          staticRR_result;

vector<IplImage *>Route_0[WordNum][5];//Picture in file folder p50
vector<IplImage *>Route_1[WordNum][5];//Picture in file folder p51
vector<IplImage *>Route_2[WordNum][5];//Picture in file folder p52
vector<IplImage *>Route_3[WordNum][5];//Picture in file folder p53
vector<IplImage *>Route_4[WordNum][5];//Picture in file folder p54

vector<double>HOG_0[WordNum][5][25];//HOG feature for each key frame.
vector<double>HOG_1[WordNum][5][25];
vector<double>HOG_2[WordNum][5][25];
vector<double>HOG_3[WordNum][5][25];
vector<double>HOG_4[WordNum][5][25];

//ofstream marrytxt;

void LBP (IplImage *src,IplImage *dst)
{
	int tmp[8]={0};
	CvScalar s;
	IplImage * temp = cvCreateImage(cvGetSize(src), IPL_DEPTH_8U,1);
	uchar *data=(uchar*)src->imageData;
	int step=src->widthStep;
	for (int i=1;i<src->height-1;i++)
		for(int j=1;j<src->width-1;j++)
		{
			int sum=0;
			if(data[(i-1)*step+j-1]>data[i*step+j])
				tmp[0]=1;
			else
				tmp[0]=0;
			if(data[i*step+(j-1)]>data[i*step+j])
				tmp[1]=1;
			else
				tmp[1]=0;
			if(data[(i+1)*step+(j-1)]>data[i*step+j])
				tmp[2]=1;
			else
				tmp[2]=0;
			if (data[(i+1)*step+j]>data[i*step+j])
				tmp[3]=1;
			else
				tmp[3]=0;
			if (data[(i+1)*step+(j+1)]>data[i*step+j])
				tmp[4]=1;
			else
				tmp[4]=0;
			if(data[i*step+(j+1)]>data[i*step+j])
				tmp[5]=1;
			else
				tmp[5]=0;
			if(data[(i-1)*step+(j+1)]>data[i*step+j])
				tmp[6]=1;
			else
				tmp[6]=0;
			if(data[(i-1)*step+j]>data[i*step+j])
				tmp[7]=1;
			else
				tmp[7]=0;
			for(int k=0;k<=7;k++)
				sum+=abs(tmp[k]-tmp[k+1]);
			sum=sum+abs(tmp[7]-tmp[0]);
			if (sum<=2)
				s.val[0]=(tmp[0]*1+tmp[1]*2+tmp[2]*4+tmp[3]*8+tmp[4]*16+tmp[5]*32+tmp[6]*64+tmp[7]*128);
			else s.val[0]=10; 
			cvSet2D(dst,i,j,s);
		}
}

//Return Euclidean distance of two images.
double img_distance(IplImage *dst1,IplImage *dst2)
{
	int i,j;
	uchar *ptr1;
	uchar *ptr2;

	double result=0.0;////////////
	for(i=0;i<dst1->height;i++)
	{
		ptr1=(uchar *)(dst1->imageData+i*dst1->widthStep);
		ptr2=(uchar *)(dst2->imageData+i*dst2->widthStep);

		for(j=0;j<dst1->width;j++)
			result+=(ptr1[j*dst1->nChannels]-ptr2[j*dst2->nChannels])*(ptr1[j*dst1->nChannels]-ptr2[j*dst2->nChannels]);
	}
	result=sqrt(result);
	return result;
}

//Overloaded function for sorting.
bool _cmp(Std pp,Std qq)
{
	return pp.std_distance<qq.std_distance;
}

//Using the resize function in OpenCV.
IplImage *Resize(IplImage *_img)
{
	IplImage *_dst=cvCreateImage(cvSize(SIZE,SIZE),_img->depth,_img->nChannels);
	cvResize(_img,_dst);
	return _dst;
}

//Data reading: images according to the chooseno. To fill the choose_pic.
void TraverseAllRoute(CString BaseRoute,vector<IplImage *> Route[WordNum][5],vector<int>chooseno)
{
	WIN32_FIND_DATA FileData;
	vector<int>::iterator pointer;
	HANDLE handle=FindFirstFile(BaseRoute+Add,&FileData);

	if(handle==INVALID_HANDLE_VALUE)
	{
		//cout<<"Fail to open file"<<endl;
		//exit(0);
		return ;
	}
	CString temp;
	int i,j,k,m,n;
	int Sec;
	int Lindex,Rindex;//分别表示手势序号及其对应的左手、右手和双手
	int Count_keyframe = 0;//Number of key frames.
	int a,b;//Start and end index of each key frame.
	char s[10];//Temp string
	IplImage *T_img;//
	IplImage *T_avg=cvCreateImage(cvSize(SIZE,SIZE),8,1);//Mean images
	uchar *pp;//
	uchar *qq;//
	int Sum[105][105];//Store sum of gray level

	while( FindNextFile(handle,&FileData) )
	{
		temp=FileData.cFileName;
		if( strcmp( temp.Right(3),"txt" )==0 )//Searching .txt file.
		{
			Sec=0;
			for(i=0;i<BaseRoute.GetLength();i++)
			{
				if( BaseRoute[i]=='_' )//
				{
					Sec++;
					if(Sec==1)//获取是第几个手势(手势编号)
					{
						Lindex=(BaseRoute[i+1]-48)*1000 + (BaseRoute[i+2]-48)*100 + (BaseRoute[i+3]-48)*10 + (BaseRoute[i+4]-48);
						break;
					}
				}
			}

			pointer=find(chooseno.begin(),chooseno.end(),Lindex);
			if(pointer==chooseno.end())
				;
			else
			{
				Lindex=pointer-chooseno.begin();
				if( temp[0]=='l' )//LeftHand
					Rindex=0;
				else if( temp[0]=='r' )//ightHand
					Rindex=1;
				else 
					Rindex=2;//Both

				infile.open(BaseRoute+"\\"+temp,ios::in);//Open the .txt file that searched. 
				infile>>Count_keyframe;//Input the key frame number.
				CString Temp;

				for(i=0;i<Count_keyframe;i++)
				{
					choose_pic.clear();
					memset(Sum,0,sizeof(Sum));

					infile>>a>>b;
					for(j=a;j<=b;j++)//Travel the b-a+1 images.
					{
// 						if( j>0 && j<10 )
// 							Temp=BaseRoute+"\\000"+itoa( j , s , 10 )+".jpg";
// 					    else if( j>=10 && j<100 )
// 							Temp=BaseRoute+"\\00"+itoa( j , s , 10 )+".jpg";
// 						else if( j>=100 )
// 							Temp=BaseRoute+"\\0"+itoa( j , s , 10 )+".jpg";

						Temp=BaseRoute+"\\"+itoa( j , s , 10 )+".jpg";

						T_img=cvLoadImage(Temp,0);
						if(T_img!=NULL)//If this image exists.
						{
// 							cvCvtColor(T_img,T_img,CV_BGR2HSV);//add by Hanjie Wang
// 							IplImage* T_img2 = cvCreateImage(cvGetSize(T_img),T_img->depth,1);
// 
// 							for (m=0;m<T_img->height;m++)
// 							{
// 								uchar* pImg1 = (uchar*)(T_img2->imageData + m*T_img2->widthStep);
// 								uchar* pImg0 = (uchar*)(T_img->imageData + m*T_img->widthStep);
// 								for (n=0;n<T_img->width;n++)
// 								{
// 									pImg1[n] = pImg0[3*n+1]; 
// 								}
// 							}
// 							T_img2=Resize(T_img2);//在这里进行size的归一化
// 							cvSmooth(T_img2,T_img2,CV_GAUSSIAN,5,3);//平滑处理，消除噪声
// 							for(m=0 ; m<T_img2->height ; m++)
// 							{
// 								pp=(uchar *)(T_img2->imageData+m*T_img2->widthStep);
// 								for(n=0;n<T_img2->width;n++)
// 								{
// 									Sum[m][n]+=pp[n*T_img2->nChannels];
// 								}
// 							}
// 							p_std=new Std(T_img2);
							T_img=Resize(T_img);//Size normalization
							cvSmooth(T_img,T_img,CV_GAUSSIAN,5,3);//Smoothing
							for(m=0 ; m<T_img->height ; m++)
							{
								pp=(uchar *)(T_img->imageData+m*T_img->widthStep);
								for(n=0;n<T_img->width;n++)
									{
										Sum[m][n]+=pp[n*T_img->nChannels];
								}
							}
							p_std=new Std(T_img);
							choose_pic.push_back(*p_std);
						}
					}

					if(choose_pic.size()==0)
						;
					else
					{
						for(m=0;m<SIZE;m++)
						{
							qq=(uchar *)(T_avg->imageData+m*T_avg->widthStep);
							for(n=0;n<SIZE;n++)
							{
								Sum[m][n]=Sum[m][n]/choose_pic.size();
								qq[n*T_avg->nChannels]=Sum[m][n];
							}
						}
						for(k=0;k<choose_pic.size();k++)
							choose_pic[k].std_distance=img_distance(choose_pic[k].pic_route,T_avg);
						sort(choose_pic.begin(),choose_pic.end(),_cmp);//Sort the x images by the distance to s.
						Route[Lindex][Rindex].push_back(choose_pic[0].pic_route);
					}
				}
				infile.close();
			}
		}
		if( strcmp(temp,"..") )
		{
			TraverseAllRoute(BaseRoute+"\\"+temp,Route,chooseno);
		}
	}
}

//Get the hog feature of images.
bool GetHOGHistogram_Patch(IplImage *img,vector<double> &hog_hist)
{
	HOGDescriptor *hog=new HOGDescriptor(cvSize(SIZE,SIZE),cvSize(16,16),cvSize(8,8),cvSize(8,8),9);
	//HOGDescriptor *hog=new HOGDescriptor(cvSize(SIZE,SIZE),cvSize(32,32),cvSize(16,16),cvSize(16,16),9);
	//(cvSize(SIZE,SIZE),cvSize(16,16),cvSize(8,8),cvSize(8,8),9)
	/////////////////////window: 64*64，block: 8*8，block step:4*4，cell: 4*4
	cvNormalize(img,img,255,0,CV_MINMAX,0); //Add by Hanjie Wang. 2013-03.
	//LBP(img,img);
	Mat handMat(img);

	vector<float> *descriptors = new std::vector<float>();

	hog->compute(handMat, *descriptors,Size(0,0), Size(0,0));
	////////////////////window: 0*0
	double total=0;
	int i;
	for(i=0;i<descriptors->size();i++)
		total+=abs((*descriptors)[i]);
	//	total=sqrt(total);
	for(i=0;i<descriptors->size();i++)
		hog_hist.push_back((*descriptors)[i]/total);
	return true; 
}

//Measuring two HOG features.
double Histogram(vector<double>vec1,vector<double>vec2)
{
	double mat_score=0.0;//mat_score: similarity
	int i;
	int _Size=vec1.size();
	for(i=0;i<_Size;i++)
	{
		mat_score+=vec1[i]<vec2[i] ? vec1[i] : vec2[i];
// 		if (vec1[i]!=0 && vec2[i]!=0)
// 		{
// 			mat_score+=((vec1[i]-vec2[i])*(vec1[i]-vec2[i])/(vec1[i]+vec2[i]));  //the smaller, the best.
// 		}
		
	}
	return  mat_score;
}

//Out put all the combination of C(n,m)
void Combination(int pos,int m,int n)
{
	int i;
	if(m==0)
	{
		for(i=1;i<=c_choice;i++)
			combination[_count][i]=_temp[i];
		_count++;
		return ;
	}
	if(m>n)
		return ;
	if(n==0)
		return ;																								
	_temp[pos]=n-1; //Very important
	Combination(pos-1,m-1,n-1);
	Combination(pos,m,n-1);
}

double Posture_Distance2(vector<double>xx[],int x,vector<double>yy[],int y)
{
	double Max=0.0;
	if(x==0 || y==0)//No key frames in both
	{
		return 0.0;
	}
	if(x>15 || y>15)//Number of key frames>15 will be consider as abnormal.
	{
		return 0.0;
	}
	int i,j;
	double result;
	_count=0;
	//////////////////////////////////////////////////////////////////////////
	//Hanjie Wang. 2013-03.
	//Match: X->Y
	int*    order =     new int[x];
	double* weight =    new double[x];
	int*    maxLength = new int[x];
	for (i=0; i<x; i++)
	{
		*(maxLength+i) = 1;
	}
		//Calculate the maximum weight and its order.
	for (i=0; i<x; i++)
	{
		double maxMatch = 0.0;
		for (j=0; j<y; j++)
		{
			double tempMatch = Histogram(xx[i],yy[j]);
			if (tempMatch>maxMatch)
			{
				maxMatch = tempMatch;
				*(order+i)= j;
			}
		}
		*(weight+i) = maxMatch;
	}
		//Obtain the maxLength for each Index
	for (i=1; i<x; i++)
	{
		for (j=i-1; j>=0; j--)
		{
			if (*(order+i)>*(order+j))
			{
				*(maxLength+i) = *(maxLength+j)+1;
				break;
			}
		}
	}
		//Get the Index with max length.
	int maxLengthIndex = 0;
	for (i=1; i<x; i++)
	{
		if (*(maxLength+i)>*(maxLength+maxLengthIndex))
		{
			maxLengthIndex = i;
		}
	}
		//Computer the average weight by back tracing.
	double aveWeight = 0.0;
	aveWeight += *(weight+maxLengthIndex);
	for (i=maxLengthIndex; i>=0;)
	{
		for (j=i; j>=0; j--)
		{
			if (*(order+j)<*(order+i))
			{
				aveWeight += *(weight+j);
				i=j;
				break;
			}
			else if (j==0)
			{
				i=-1;
				break;
			}
		}
	}
	aveWeight = aveWeight/(*(maxLength+maxLengthIndex));

	delete[] order;
	delete[] weight;
	delete[] maxLength;

	//////////////////////////////////////////////////////////////////////////
	//Hanjie Wang. 2013-03.
	//Match: Y->X
	int*    order2 =     new int[y];
	double* weight2 =    new double[y];
	int*    maxLength2 = new int[y];
	for (i=0; i<y; i++)
	{
		*(maxLength2+i) = 1;
	}
	//Calculate the maximum weight and its order.
	for (i=0; i<y; i++)
	{
		double maxMatch = 0.0;
		for (j=0; j<x; j++)
		{
			double tempMatch = Histogram(yy[i],xx[j]);
			if (tempMatch>maxMatch)
			{
				maxMatch = tempMatch;
				*(order2+i)= j;
			}
		}
		*(weight2+i) = maxMatch;
	}
	//Obtain the maxLength for each Index
	for (i=1; i<y; i++)
	{
		for (j=i-1; j>=0; j--)
		{
			if (*(order2+i)>*(order2+j))
			{
				*(maxLength2+i) = *(maxLength2+j)+1;
				break;
			}
		}
	}
	//Get the Index with max length.
	maxLengthIndex = 0;
	for (i=1; i<y; i++)
	{
		if (*(maxLength2+i)>*(maxLength2+maxLengthIndex))
		{
			maxLengthIndex = i;
		}
	}
	//Computer the average weight by back tracing.
	double aveWeight2 = 0.0;
	aveWeight2 += *(weight2+maxLengthIndex);
	for (i=maxLengthIndex; i>=0;)
	{
		for (j=i; j>=0; j--)
		{
			if (*(order+j)<*(order+i))
			{
				aveWeight2 += *(weight2+j);
				i=j;
				break;
			}
			else if (j==0)
			{
				i=-1;
				break;
			}
		}
	}
	aveWeight2 = aveWeight2/(*(maxLength2+maxLengthIndex));

	delete[] order2;
	delete[] weight2;
	delete[] maxLength2;
	//////////////////////////////////////////////////////////////////////////
	aveWeight = aveWeight>aveWeight2?aveWeight:aveWeight2;

	return aveWeight;

	//////////////////////////////////////////////////////////////////////////
/*	if(x<=y)
	{
		c_choice=x;
		c_total=y;
		Combination(x,x,y);
		for(i=0;i<_count;i++)
		{
			result=0;
			for(j=0;j<x;j++)
				result+=Histogram( xx[j],yy[ combination[i][j+1] ] );
			if(result>Max)
				Max=result;
		}
		Max=Max/x;  //Normalization
	}
	else
	{
		c_choice=y;
		c_total=x;
		Combination(y,y,x);
		for(i=0;i<_count;i++)
		{
			result=0;
			for(j=0;j<y;j++)
				result+=Histogram( xx[ combination[i][j+1] ],yy[j] );
			if(result>Max)
				Max=result;
		}
		Max=Max/y;  //Normalization
	}

	return Max;
*/
}

double Posture_Distance(vector<double>xx[],int x,vector<double>yy[],int y, int *pairSum)
{
	if(x==0 || y==0)//No key frames in both
	{
		return 0.0;
	}
	if(x>15 || y>15)//Number of key frames>15 will be consider as abnormal.
	{
		return 0.0;
	}
	int i,j;
	int*    order =     new int[x];
	double* weight =    new double[x];
	int*    maxLength = new int[x];

	for (i=0; i<x; i++)
	{
		*(maxLength+i) = 1;
	}
		//Calculate the maximum weight and its order.
	for (i=0; i<x; i++)
	{
		double maxMatch = 0.0;
		for (j=0; j<y; j++)
		{
			double tempMatch = Histogram(xx[i],yy[j]);
			if (tempMatch>maxMatch)
			{
				maxMatch = tempMatch;
				*(order+i)= j;
			}
		}
		*(weight+i) = maxMatch;
	}
		//Obtain the maxLength for each Index
	for (i=1; i<x; i++)
	{
		int maxlengthTemp = 0;
		for (j=i-1; j>=0; j--)
		{
			if (*(order+i)>*(order+j))
			{
				if (*(maxLength+j)>maxlengthTemp)
				{
					*(maxLength+i) = *(maxLength+j)+1;
					maxlengthTemp = *(maxLength+j);
				}
// 				*(maxLength+i) = *(maxLength+j)+1;
// 				break;
			}
		}
	}
		//Get the max length of all
	int maxLengthAll = 0;
	for (i=0; i<x; i++)
	{
		if (*(maxLength+i)>maxLengthAll)
		{
			maxLengthAll = *(maxLength+i);
		}
	}
	int routeNo = 1;
	int* group = new int[maxLengthAll*x];   //At most x element in one group.
	int* groupNo = new int[maxLengthAll];   
	memset(groupNo,0,maxLengthAll*sizeof(int));
	for (i=0; i<maxLengthAll; i++)
	{
		for (j=0; j<x; j++)
		{
			if (*(maxLength+j) == i+1)
			{
				*(group + i*x + (*(groupNo + i)))=j;
				*(groupNo + i) += 1;
			}
		}
		routeNo *= (*(groupNo + i));
	}

	int* routeAll = new int[routeNo*maxLengthAll];         
	int step = 1;
	for (i=0; i<maxLengthAll; i++)
	{
		for (j=0; j<routeNo; j++)
		{
			double jChange = j/step;
			int jFloor = floor(jChange);
			int groIndex = (jFloor)%(*(groupNo + i));
			*(routeAll+j*maxLengthAll+i) = *(group+i*x+groIndex);
		}
		step = *(groupNo + i);
	}

	//To search the routeAll and find the legal and largest one.
	//Indexes are stored in routeAll.
	//*(weight+index)is its weight.
	//*(order+index)is its order. Both of its "order" and "index" should in order.

	double maxWeight = 0.0;
	for (i=0; i<routeNo; i++)
	{
		bool useful = true;
		double weightTempSum = 0.0;
		for (j=0; j<maxLengthAll-1; j++)
		{
			int former = *(routeAll+i*maxLengthAll+j);
			int latter = *(routeAll+i*maxLengthAll+j+1);
			weightTempSum += *(weight + former);
			if (former>latter || *(order+former)>*(order+latter))
			{
				useful = false;
			}
		}
		if (useful)
		{
			weightTempSum += *(weight+maxLengthAll-1);
			if (weightTempSum>maxWeight)
			{
				maxWeight = weightTempSum;
			}
		}
	}

	maxWeight /= maxLengthAll;
	(*pairSum) = maxLengthAll;

	delete[] groupNo;
	delete[] group;
	delete[] routeAll;
	delete[] order;
	delete[] weight;
	delete[] maxLength;

	maxWeight = maxWeight + (maxLengthAll-1)*0.0; //0.03 can been tuned.
	return maxWeight>1?1:maxWeight;
}

double Posture_Distance_new(vector<double>probe[],int probeNo,vector<double>gallery[],int galleryNo, int *pairSum)
{
	int m, n, k;
	int pairNum = probeNo*galleryNo;

	vector<Pair> myPair;
	for (m=0; m<probeNo; m++)
	{
		for (n=0; n<galleryNo; n++)
		{
			Pair tempPair;
			tempPair.man = m;
			tempPair.woman = n;
			tempPair.love = Histogram(probe[m],gallery[n]);
			tempPair.married = 2;
			myPair.push_back(tempPair);
		}
	}

	//////////////////////////////////////////////////////////////////////////
	//Find the hog_final from myPair.
	int Maybe_num = 0;
	for (k=0; k<pairNum; k++)
	{
		if (myPair[k].married == 2)
		{
			Maybe_num++;
		}
	}
	//Label the married.
	while (Maybe_num > 0)
	{
		//Find the largest love and marry them.
		double max = 0.0;
		int maxIndex = 0;
		for (k=0; k<pairNum; k++)
		{
			if (myPair[k].married==2 && myPair[k].love >= max)
			{
				max = myPair[k].love;
				maxIndex = k;
			}
		}

		if (myPair[maxIndex].love > MarryThre)
		{
			myPair[maxIndex].married = 1;

			//Unmarried the related others. 
			for (k=0; k<pairNum; k++)
			{
				if (k!=maxIndex)
				{
					bool sad = false;   //If sad is true, they will be unmarried (0).
					if (myPair[k].man == myPair[maxIndex].man)
					{
						sad = true;
					}
					if (myPair[k].woman == myPair[maxIndex].woman)
					{
						sad = true;
					}
					if (myPair[k].man > myPair[maxIndex].man && myPair[k].woman < myPair[maxIndex].woman)
					{
						sad = true;
					}
					if (myPair[k].man < myPair[maxIndex].man && myPair[k].woman > myPair[maxIndex].woman)
					{
						sad = true;
					}
					if (sad)
					{
						myPair[k].married = 0;  //They can not be married.
					}
				}
			}

			Maybe_num = 0;
			for (k=0; k<pairNum; k++)
			{
				if (myPair[k].married == 2)
				{
					Maybe_num++;
				}
			}
		}
		else
		{
			for (k=0; k<pairNum; k++)
			{
				if (myPair[k].married == 2)
				{
					myPair[k].married = 0;
				}
			}

			break;
		}
	}

	double weight = 0.0;
	int marryNo = 0;
	for (k=0; k<pairNum; k++)
	{
		if (myPair[k].married == 1)
		{
			weight += myPair[k].love;
			marryNo++;
		}
	}
	(*pairSum) = marryNo;

	double outputW;
	if (marryNo == 0)
	{
		outputW = weight;
	}
	else
	{
		outputW = weight/marryNo;
	}
	return outputW;
}

bool cmp(Rank a,Rank b)
{
	return a.distance>b.distance;
}

double Max(double a,double b,double c,double d)
{
	return max( max(a,b),max(c,d) );
}

void ReadData(CString Testdata, int Posture_num,vector<int>chooseno, 
	int ikeyFrameNo[][5], vector<IplImage*>Route_0[][5], vector<double>HOG_0[][5][25], int folderIndex)
{
	int i,j,k;
	CString folderName;
	//folderName.Format(folderIndex);
	folderName.Format("%d", folderIndex);
	//CString::Format(folderName,folderIndex);
	TraverseAllRoute("D:\\iData\\Kinect sign data\\Test\\"+Testdata+"\\P"+folderName,Route_0,chooseno);
	cout<<"("<<folderIndex<<")Route searching of file p"<<folderIndex<< " is finished."<<endl;
	for(i=0;i<Posture_num;i++)
		for(j=0;j<LRB;j++)
		{
			ikeyFrameNo[i][j] = Route_0[i][j].size();
			for(k=0;k<Route_0[i][j].size();k++)
				GetHOGHistogram_Patch(Route_0[i][j][k],HOG_0[i][j][k]);
		}
		cout<<"("<<folderIndex<<")HOG features in file p"<<folderIndex<< " have been computed."<<endl;
}

void lastDistance(int Posture_num, double* Last_Distance10, double* Last_Distance01, int* pairSumMatrix10, int* pairSumMatrix01, 
	int keyFrameNo0[][5], int keyFrameNo1[][5], 
	vector<double> HOG_0[][5][25], vector<double> HOG_1[][5][25])
{
	double dou_temp;
	int i, j, y, k;
	memset(Last_Distance10,0,Posture_num*Posture_num*sizeof(double));//
	memset(pairSumMatrix10,0,Posture_num*Posture_num*sizeof(int));//
	memset(pairSumMatrix01,0,Posture_num*Posture_num*sizeof(int));//
	for(i=0;i<Posture_num;i++)
	{
		//clock_t start, durTime;
		//start=clock();
		//int keyCount = 0;
		for(j=0;j<Posture_num;j++)
		{
			//int pairSum10;
			int pairSum;
			for(k=0;k<FusedLRB;k++)
			{
				int keyFrame0 = keyFrameNo0[i][k];
				int keyFrame1 = keyFrameNo1[j][k];
				//keyCount+=keyFrame1;
				//pairSum10 = 0;
				pairSum = 0;
//  				dou_temp=max(Posture_Distance(HOG_1[i][k], keyFrame1, HOG_0[j][k], keyFrame0, &pairSum10),
//  					Posture_Distance(HOG_0[j][k], keyFrame0, HOG_1[i][k], keyFrame1, &pairSum01));
				dou_temp=Posture_Distance_new(HOG_0[i][k], keyFrame0, HOG_1[j][k], keyFrame1, &pairSum);

				(*(Last_Distance01 + i*Posture_num + j))+=dou_temp;
				(*(pairSumMatrix01 + i*Posture_num + j))+= pairSum;
			}
			if ((*(Last_Distance01 + i*Posture_num + j)) <0 )
			{
				*(Last_Distance01 + i*Posture_num + j) = 0;
			}
			(*(Last_Distance10 + j*Posture_num + i))=(*(Last_Distance01 + i*Posture_num + j));
			(*(pairSumMatrix10 + j*Posture_num + i))=(*(pairSumMatrix01 + i*Posture_num + j));
		}
		//durTime=clock()-start;
		//cout<<"Compare 370 Times:	"<<durTime<<"frame No: "<<keyCount<<endl;
		//Sleep(1000);
	}
}

void recognitionRateTest(int Posture_num, double* Last_Distance01,double* Last_Distance02,
	double* Last_Distance03,double* Last_Distance04,int *pairSumMatrix01, 
	int *pairSumMatrix02,int *pairSumMatrix03,int *pairSumMatrix04,
	ofstream &outfile00, int outputLine)
{
	int i,j;
	int Num1,Num3,Num5,Num10;
	double Rank1,Rank3,Rank5,Rank10;
	double* Last_Distance = new double[Posture_num*Posture_num];

	for(i=0;i<Posture_num;i++)
	{
			//Get the max pair number.
		int maxPairSum = 0;
		for (j=0; j<Posture_num; j++)
		{
			int pairSum[4];
			pairSum[0] = *(pairSumMatrix01+i*Posture_num+j);
			pairSum[1] = *(pairSumMatrix02+i*Posture_num+j);
			pairSum[2] = *(pairSumMatrix03+i*Posture_num+j);
			pairSum[3] = *(pairSumMatrix04+i*Posture_num+j);
			int maxPairSumTemp = max(max(pairSum[0],pairSum[1]),max(pairSum[2],pairSum[3]));
			if (maxPairSumTemp>maxPairSum)
			{
				maxPairSum = maxPairSumTemp;
			}
		}
		for(j=0;j<Posture_num;j++)
		{
			int maxPairSumTemp2 = max(max(*(pairSumMatrix01+i*Posture_num+j),*(pairSumMatrix02+i*Posture_num+j)),
				max(*(pairSumMatrix03+i*Posture_num+j),*(pairSumMatrix04+i*Posture_num+j)));
			//if (maxPairSumTemp2 == maxPairSum)    //Delete the code. Because RR decreases. 
			{
				double scoPo[4];
				scoPo[0] = *(Last_Distance01+i*Posture_num+j)+ (*(pairSumMatrix01+i*Posture_num+j))*PairSumBonus;
				scoPo[1] = *(Last_Distance02+i*Posture_num+j)+ (*(pairSumMatrix02+i*Posture_num+j))*PairSumBonus;
				scoPo[2] = *(Last_Distance03+i*Posture_num+j)+ (*(pairSumMatrix03+i*Posture_num+j))*PairSumBonus;
				scoPo[3] = *(Last_Distance04+i*Posture_num+j)+ (*(pairSumMatrix04+i*Posture_num+j))*PairSumBonus;
				double sumSco = scoPo[0] + scoPo[1] + scoPo[2] + scoPo[3];
				double maxSco = Max(scoPo[0], scoPo[1], scoPo[2], scoPo[3]);
				double minSco = min(min(scoPo[0], scoPo[1]),min(scoPo[2], scoPo[3]));
				double maxSco2 = 0.0;
				for (int k=0; k<4; k++)
				{
					if (scoPo[k] != maxSco && scoPo[k]>maxSco2)
					{
						maxSco2 = scoPo[k];
					}
				}

				if (maxSco2>2.0)
				{
					*(Last_Distance+i*Posture_num+j)= (maxSco+maxSco2)/2;
				}
				else
				{
					*(Last_Distance+i*Posture_num+j)= maxSco;
				}

				// 			double aveSco = (*(Last_Distance01+i*Posture_num+j)+*(Last_Distance02+i*Posture_num+j)+
				// 				*(Last_Distance03+i*Posture_num+j)+*(Last_Distance04+i*Posture_num+j))/4;
				// 			double ScoVari = (4*maxSco - 4*aveSco)/3;
				// 			if (ScoVari>100.00)
				// 			{
				// 				*(Last_Distance+i*Posture_num+j)=aveSco;
				// 			}
				// 			else
				// 			{
				// 				*(Last_Distance+i*Posture_num+j)=maxSco;
				// 			}

				double temp = *(Last_Distance+i*Posture_num+j);
				//outfile00<<temp<<","<<maxPairSumTemp2<<",";
				outfile00<<temp<<'\t';
// 				outfile00<<temp<<","<<*(pairSumMatrix01+i*Posture_num+j)<<" "<<*(pairSumMatrix02+i*Posture_num+j)<<" "<<
// 					*(pairSumMatrix03+i*Posture_num+j)<<" "<<*(pairSumMatrix04+i*Posture_num+j)<<",";
			}
			
		}
		outfile00<<endl;
	}
	Num1=0;
	Num3=0;
	Num5=0;
	Num10=0;
	for(i=0;i<Posture_num;i++)
	{
		Last_temp.clear();
		for(j=0;j<Posture_num;j++)
		{
			p=new Rank(j,*(Last_Distance+i*Posture_num+j));
			Last_temp.push_back(*p);
		} 
		sort(Last_temp.begin(),Last_temp.end(),cmp);
		firstRankOutfile<<Last_temp[0].no<<",";
		for(j=0;j<10;j++)
		{
			if(Last_temp[j].no==i)
			{
				if(j<1)
					Num1++;
				if(j<3)
					Num3++;
				if(j<5)
					Num5++;
				if(j<10)
					Num10++;
			}
		}
	}
	firstRankOutfile<<endl;

	Rank1=100.0*Num1/Posture_num;
	Rank3=100.0*Num3/Posture_num;
	Rank5=100.0*Num5/Posture_num;
	Rank10=100.0*Num10/Posture_num;


	staticRR_result[outputLine*8+0] = Rank1;
	staticRR_result[outputLine*8+1] = Rank3;
	staticRR_result[outputLine*8+2] = Rank5;
	staticRR_result[outputLine*8+3] = Rank10;
	staticRR_result[outputLine*8+4] = Num1;
	staticRR_result[outputLine*8+5] = Num3;
	staticRR_result[outputLine*8+6] = Num5;
	staticRR_result[outputLine*8+7] = Num10;

	
// 	outfile<<"Rank1:"<<","<<Num1<<","<<Rank1<<endl;
// 	outfile<<"Rank3:"<<","<<Num3<<","<<Rank3<<endl;
// 	outfile<<"Rank5:"<<","<<Num5<<","<<Rank5<<endl;
// 	outfile<<"Rank10:"<<","<<Num10<<","<<Rank10<<endl;

	delete []Last_Distance;
}

int ReadDataFromGallery(CString route, int Gallery_num, int Posture_num, int HOG_dimension, int ikeyFrameNo[][WordNum][5],int testFlag[],
	vector<double>HOG_0[][5][25],vector<double>HOG_1[][5][25],vector<double>HOG_2[][5][25],
	vector<double>HOG_3[][5][25],vector<double>HOG_4[][5][25])
{
	int i, j, k, galleryIndex, m;
	int* Label_sequence;     //Original label sequence.
	int* Label_sequence_locate;
	double* p_gallery;           //Gallery HOG

	int labelSize = Gallery_num*Posture_num*FusedLRB;  //Label_size=5*370*3
	Label_sequence = new int[labelSize];
	Label_sequence_locate = new int[labelSize];

	ifstream infile1;
	infile1.open(route+"\\Gallery_Label.dat",ios::binary);
	infile1.read( (char *)Label_sequence, labelSize*sizeof(int) );//将Gallery_Label中的数据读到数组Label_sequence1中
	infile1.close();

	int keyFrameIntotal = 0;
	*(Label_sequence_locate+0) = *(Label_sequence + 0);
	for(i=0;i<labelSize;i++)
	{
		keyFrameIntotal += *(Label_sequence + i);
		if (i>0)
		{
			*(Label_sequence_locate+i) = *(Label_sequence_locate+i-1) + *(Label_sequence + i);
		}
	}
	cout<<"Label has been read into memory"<<endl;
	int HOGsize=keyFrameIntotal * HOG_dimension;//HOG_size
	p_gallery=new double[HOGsize];                         //p_gallery

	ifstream infile2;
	infile2.open(route+"\\Gallery_Data.dat",ios::binary);
	infile2.read((char*)p_gallery,HOGsize * sizeof(double));
	infile2.close();
	cout<<"Gallery has been read into the memory"<<endl;

	//////////////////////////////////////////////////////////////////////////
	// 	int testFlag[WordNum];
	// 	for (i=0; i<Posture_num; i++)
	// 	{
	// 		infileMask>>testFlag[i];
	// 	}
	int count;
	for (galleryIndex = 0; galleryIndex<Gallery_num; galleryIndex++)
	{
		count = 0;
		for(i=0; i<Posture_num; i++)                             //Posture
		{
			if (testFlag[i] == 1)
			{
				for(j=0;j<FusedLRB;j++)                                         //Left, right, both
				{
					ikeyFrameNo[galleryIndex][count][j] = *(Label_sequence + galleryIndex*FusedLRB*Posture_num + i*FusedLRB + j);
					int frameLocation;
					if (galleryIndex == 0 && i == 0 && j == 0)
					{
						frameLocation = 0;
					}
					else
					{
						frameLocation = *(Label_sequence_locate + galleryIndex*FusedLRB*Posture_num + i*FusedLRB + j-1);
					}

					for(k=0; k<ikeyFrameNo[galleryIndex][count][j]; k++)            //Key frame
					{
						if (galleryIndex == 0)
						{
							for (m=0; m<HOG_dimension; m++)
							{
								HOG_0[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
							}
						}
						else if (galleryIndex == 1)
						{
							for (m=0; m<HOG_dimension; m++)
							{
								HOG_1[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
							}
						}
						else if (galleryIndex == 2)
						{
							for (m=0; m<HOG_dimension; m++)
							{
								HOG_2[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
							}
						}
						else if (galleryIndex == 3)
						{
							for (m=0; m<HOG_dimension; m++)
							{
								HOG_3[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
							}
						}
						else if (galleryIndex == 4)
						{
							for (m=0; m<HOG_dimension; m++)
							{
								HOG_4[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
							}
						}
					}
				}
				count +=1;
			}
		}
		cout<<"Gallery "<<galleryIndex<<" has been read into array"<<endl;
	}



	delete[] p_gallery;
	delete[] Label_sequence;
// 	int i, j, k, galleryIndex, m;
// 	int* Label_sequence;     //Original label sequence.
// 	int* Label_sequence_locate;
// 	double* p_gallery;           //Gallery HOG
// 
// 	int labelSize = Gallery_num*Posture_num*LRB;  //Label_size=5*370*3
// 	Label_sequence = new int[labelSize];
// 	Label_sequence_locate = new int[labelSize];
// 
// 	ifstream infile1;
// 	infile1.open(route+"\\Gallery_Label.dat",ios::binary);
// 	infile1.read( (char *)Label_sequence, labelSize*sizeof(int) );//将Gallery_Label中的数据读到数组Label_sequence1中
// 	infile1.close();
// 
// 	int keyFrameIntotal = 0;
// 	*(Label_sequence_locate+0) = *(Label_sequence + 0);
// 	for(i=0;i<labelSize;i++)
// 	{
// 		keyFrameIntotal += *(Label_sequence + i);
// 		if (i>0)
// 		{
// 			*(Label_sequence_locate+i) = *(Label_sequence_locate+i-1) + *(Label_sequence + i);
// 		}
// 	}
// 	cout<<"Label has been read into memory"<<endl;
// 	int HOGsize=keyFrameIntotal * HOG_dimension;//HOG_size
// 	p_gallery=new double[HOGsize];                         //p_gallery
// 
// 	ifstream infile2;
// 	infile2.open(route+"\\Gallery_Data.dat",ios::binary);
// 	infile2.read((char*)p_gallery,HOGsize * sizeof(double));
// 	infile2.close();
// 	cout<<"Gallery has been read into the memory"<<endl;
// 
// 	//////////////////////////////////////////////////////////////////////////
// // 	int testFlag[WordNum];
// // 	for (i=0; i<Posture_num; i++)
// // 	{
// // 		infileMask>>testFlag[i];
// // 	}
// 	int count;
// 	for (galleryIndex = 0; galleryIndex<Gallery_num; galleryIndex++)
// 	{
// 		count = 0;
// 		for(i=0; i<Posture_num; i++)                             //Posture
// 		{
// 			if (testFlag[i] == 1)
// 			{
// 				for(j=0;j<LRB;j++)                                         //Left, right, both
// 				{
// 					ikeyFrameNo[galleryIndex][count][j] = *(Label_sequence + galleryIndex*LRB*Posture_num + i*LRB + j);
// 					int frameLocation;
// 					if (galleryIndex == 0 && i == 0 && j == 0)
// 					{
// 						frameLocation = 0;
// 					}
// 					else
// 					{
// 						frameLocation = *(Label_sequence_locate + galleryIndex*LRB*Posture_num + i*LRB + j-1);
// 					}
// 					
// 					for(k=0; k<ikeyFrameNo[galleryIndex][count][j]; k++)            //Key frame
// 					{
// 						if (galleryIndex == 0)
// 						{
// 							for (m=0; m<HOG_dimension; m++)
// 							{
// 								HOG_0[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
// 							}
// 						}
// 						else if (galleryIndex == 1)
// 						{
// 							for (m=0; m<HOG_dimension; m++)
// 							{
// 								HOG_1[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
// 							}
// 						}
// 						else if (galleryIndex == 2)
// 						{
// 							for (m=0; m<HOG_dimension; m++)
// 							{
// 								HOG_2[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
// 							}
// 						}
// 						else if (galleryIndex == 3)
// 						{
// 							for (m=0; m<HOG_dimension; m++)
// 							{
// 								HOG_3[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
// 							}
// 						}
// 						else if (galleryIndex == 4)
// 						{
// 							for (m=0; m<HOG_dimension; m++)
// 							{
// 								HOG_4[count][j][k].push_back(*(p_gallery + HOG_dimension*(frameLocation+k) + m));
// 							}
// 						}
// 					}
// 				}
// 				count +=1;
// 			}
// 		}
// 		cout<<"Gallery"<<galleryIndex<<"has been read into array"<<endl;
// 	}
// 
// 
// 
// 	delete[] p_gallery;
// 	delete[] Label_sequence;
	return count;
}

void saveKeyFrame(int Posture_num, int dataIndex, vector<IplImage*>Route[][5])
{
	int i,j,k;
	CString s_filefolder;
	CString s_ImgFileName;
	int posture;
	for (i=0; i<Posture_num; i++)
	{
		for(j=0;j<LRB;j++)
		{
			for(k=0;k<Route[i][j].size();k++)
			{
				if (Route[i][j][k]!=NULL)
				{
					s_filefolder.Format("D:\\iData\\Kinect sign data\\Test\\20130428\\keyFrame\\P%d\\%d",dataIndex,i);
					_mkdir(s_filefolder);//Create the folder.
					if (j==0)
					{
						s_ImgFileName.Format("D:\\iData\\Kinect sign data\\Test\\20130428\\keyFrame\\P%d\\%d\\left_%d.jpg",dataIndex,i,k);
					}
					else if (j==1)
					{
						s_ImgFileName.Format("D:\\iData\\Kinect sign data\\Test\\20130428\\keyFrame\\P%d\\%d\\right_%d.jpg",dataIndex,i,k);
					}
					else if (j==2)
					{
						s_ImgFileName.Format("D:\\iData\\Kinect sign data\\Test\\20130428\\keyFrame\\P%d\\%d\\both_%d.jpg",dataIndex,i,k);
					}
					
					cvSaveImage(s_ImgFileName, Route[i][j][k]);
				}

			}
		}
	}
	
}

int main()
{
	int i,j,k;
	int x,y;
	bool readFromSavedGallery = true;
	int Posture_num;
	int  keyFrameNo[5][WordNum][5];
	CString routeGallery;
// 	cout<<"Please choose the dataset (data1.txt,data2.txt,data3.txt)："<<endl;
// 	char t[10];
// 	CString testdata;    //File name of dataset to be tested.
// 	cin>>t;
// 	testdata=t;
	CString testdata;
	testdata = "data3.txt";         //data3.txt has all the 370 gestures.                                          
	CString testdataMask;
	//fMaskAllData,fMask_Yili,fMask_Yushun 
	testdataMask = "fMaskAllData_1000.txt";  
// 	if( strcmp(testdata,"data1.txt")==0 )
// 	{
// 		outfile<<"Static gestures 51:"<<endl;
// 	}
// 	else if(strcmp(testdata,"data2.txt")==0)
// 	{
// 		outfile<<"Gestures 239:"<<endl;
// 	}
// 	else if(strcmp(testdata,"data3.txt")==0)
// 	{
// 		outfile<<"Gestures 370:"<<endl;
// 	}
// 	else if(strcmp(testdata,"dataStatic.txt")==0)
// 	{
// 		outfile<<"Static Gestures:"<<endl;
// 	}
// 	else
// 	{
// 		cout<<"No such dataset!"<<endl;
// 		exit(0);
// 	}
	CString TestdataFolder;
// 	cout<<"Please input the file folder:"<<endl;
// 	cin>>t;
// 	Testdata=t;
// 	if( strcmp(Testdata,"20130106") && strcmp(Testdata,"20130109") && strcmp(Testdata,"20130114") && strcmp(Testdata,"20130124") && strcmp(Testdata,"20130128") )
// 	{
// 		cout<<"No such file folder!"<<endl;
// 		exit(0);
// 	}
	TestdataFolder = "20131024"; 

	vector<int>chooseno;          //Store gesture No. in the dataset.
	infile.open("D:\\iData\\Kinect sign data\\Test\\"+testdata,ios::in);
	infileMask.open("D:\\iData\\Kinect sign data\\Test\\"+testdataMask,ios::in); //1: static gesture. 0: not static gesture.
	outfile.open("D:\\iCode\\SignLanKinectCode\\staticRR\\test.csv",ios::out);     //Show the result
	routeGallery="D:\\iData\\Kinect sign data\\NewGallery_LRToOne_20130630";//NewGallery_LRToOne_20130523

	if (readFromSavedGallery)
	{
			//Read data from saved files in discs.
		int testFlag[WordNum];
		for (i=0; i<WordNum; i++)
		{
			infileMask>>testFlag[i];
		}
		Posture_num = ReadDataFromGallery(routeGallery, 5, WordNum, 1764, keyFrameNo,testFlag,HOG_0,HOG_1,HOG_2,HOG_3,HOG_4);//1764
	}
	else
	{
			//Read the gesture No. to be processed.
		Posture_num = 0;
		while(infile>>x)
		{
			infileMask>>y;
			if (y==1)
			{
				chooseno.push_back(x);
				Posture_num+=1;
			}
		}
		Posture_num--;
			//Read data from dataset. Route and HOG assigned.
		ReadData(TestdataFolder,Posture_num,chooseno,keyFrameNo[0],Route_0,HOG_0,50);
		ReadData(TestdataFolder,Posture_num,chooseno,keyFrameNo[1],Route_1,HOG_1,51);
		ReadData(TestdataFolder,Posture_num,chooseno,keyFrameNo[2],Route_2,HOG_2,52);
		ReadData(TestdataFolder,Posture_num,chooseno,keyFrameNo[3],Route_3,HOG_3,53);
		ReadData(TestdataFolder,Posture_num,chooseno,keyFrameNo[4],Route_4,HOG_4,54);
			//Save the keyframes for checking.
// 		saveKeyFrame(Posture_num, 50, Route_0);
// 		saveKeyFrame(Posture_num, 51, Route_1);
// 		saveKeyFrame(Posture_num, 52, Route_2);
// 		saveKeyFrame(Posture_num, 53, Route_3);
// 		saveKeyFrame(Posture_num, 54, Route_4);
	}


		//Compute the distance matrix.
	double* lastDistanceMatrix[20];
	int* pairSumMatrix[20];
	//Matrix pair and their corresponding index.
	//10 20 21 30 31 32 40 41 42 43 01 02 12 03 13 23 04 14 24 34
	//0  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15 16 17 18 19
	for (i=0; i<20; i++)
	{
		lastDistanceMatrix[i] = new double[Posture_num*Posture_num];
		pairSumMatrix[i] = new int[Posture_num*Posture_num];
	}
	cout<<"1 0 && 0 1"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[0], lastDistanceMatrix[10], pairSumMatrix[0], pairSumMatrix[10],
		keyFrameNo[0], keyFrameNo[1],HOG_0,HOG_1 );
	cout<<"2 0 && 0 2"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[1], lastDistanceMatrix[11], pairSumMatrix[1], pairSumMatrix[11],
		keyFrameNo[0], keyFrameNo[2],HOG_0,HOG_2 );
	cout<<"2 1 && 1 2"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[2], lastDistanceMatrix[12], pairSumMatrix[2], pairSumMatrix[12],
		keyFrameNo[1], keyFrameNo[2],HOG_1,HOG_2 );
	cout<<"3 0 && 0 3"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[3], lastDistanceMatrix[13], pairSumMatrix[3], pairSumMatrix[13],
		keyFrameNo[0], keyFrameNo[3],HOG_0,HOG_3 );
	cout<<"3 1 && 1 3"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[4], lastDistanceMatrix[14], pairSumMatrix[4], pairSumMatrix[14],
		keyFrameNo[1], keyFrameNo[3],HOG_1,HOG_3 );
	cout<<"3 2 && 2 3"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[5], lastDistanceMatrix[15], pairSumMatrix[5], pairSumMatrix[15],
		keyFrameNo[2], keyFrameNo[3],HOG_2,HOG_3 );
	cout<<"4 0 && 0 4"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[6], lastDistanceMatrix[16], pairSumMatrix[6], pairSumMatrix[16],
		keyFrameNo[0], keyFrameNo[4],HOG_0,HOG_4 );
	cout<<"4 1 && 1 4"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[7], lastDistanceMatrix[17], pairSumMatrix[7], pairSumMatrix[17],
		keyFrameNo[1], keyFrameNo[4],HOG_1,HOG_4 );
	cout<<"4 2 && 2 4"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[8], lastDistanceMatrix[18], pairSumMatrix[8], pairSumMatrix[18],
		keyFrameNo[2], keyFrameNo[4],HOG_2,HOG_4 );
	cout<<"4 3 && 3 4"<<endl;
	lastDistance(Posture_num,lastDistanceMatrix[9], lastDistanceMatrix[19], pairSumMatrix[9], pairSumMatrix[19],
		keyFrameNo[3], keyFrameNo[4],HOG_3,HOG_4 );
	cout<<"Distance Matrix is complete now!"<<endl;

		//Recognition rate testing.
	//For output result.
	ofstream outfile50; 
	ofstream outfile51; 
	ofstream outfile52; 
	ofstream outfile53; 
	ofstream outfile54;
	outfile50.open("D:\\iCode\\SignLanKinectCode\\staticRR\\lastDistanceMatrix\\p50.txt",ios::out); 
	outfile51.open("D:\\iCode\\SignLanKinectCode\\staticRR\\lastDistanceMatrix\\p51.txt",ios::out); 
	outfile52.open("D:\\iCode\\SignLanKinectCode\\staticRR\\lastDistanceMatrix\\p52.txt",ios::out); 
	outfile53.open("D:\\iCode\\SignLanKinectCode\\staticRR\\lastDistanceMatrix\\p53.txt",ios::out); 
	outfile54.open("D:\\iCode\\SignLanKinectCode\\staticRR\\lastDistanceMatrix\\p54.txt",ios::out); 

	firstRankOutfile.open("D:\\iCode\\SignLanKinectCode\\staticRR\\firstRank.csv",ios::out); 

	staticRR_result = new double[6*8];  //The structure of output
	//outfile<<"gallery are P51 P52 P53 P54; probe is P50, Number, Percent"<<endl;
	recognitionRateTest(Posture_num, lastDistanceMatrix[10],lastDistanceMatrix[11],
		lastDistanceMatrix[13],lastDistanceMatrix[16],
		pairSumMatrix[10],pairSumMatrix[11],pairSumMatrix[13],pairSumMatrix[16],outfile50,0);
	//outfile<<"gallery are P50 P52 P53 P54; probe is P51, Number, Percent"<<endl;
	recognitionRateTest(Posture_num, lastDistanceMatrix[0],lastDistanceMatrix[12],
		lastDistanceMatrix[14],lastDistanceMatrix[17],
		pairSumMatrix[0],pairSumMatrix[12],pairSumMatrix[14],pairSumMatrix[17],outfile51,1);
	//outfile<<"gallery are P50 P51 P53 P54; probe is P52, Number, Percent"<<endl;
	recognitionRateTest(Posture_num, lastDistanceMatrix[1],lastDistanceMatrix[2],
		lastDistanceMatrix[15],lastDistanceMatrix[18],
		pairSumMatrix[1],pairSumMatrix[2],pairSumMatrix[15],pairSumMatrix[18],outfile52,2);
	//outfile<<"gallery are P50 P51 P52 P54; probe is P53, Number, Percent"<<endl;
	recognitionRateTest(Posture_num, lastDistanceMatrix[3],lastDistanceMatrix[4],
		lastDistanceMatrix[5],lastDistanceMatrix[19],
		pairSumMatrix[3],pairSumMatrix[4],pairSumMatrix[5],pairSumMatrix[19],outfile53,3);
	//outfile<<"gallery are P50 P51 P52 P53; probe is P54, Number, Percent"<<endl;
	recognitionRateTest(Posture_num, lastDistanceMatrix[6],lastDistanceMatrix[7],
		lastDistanceMatrix[8],lastDistanceMatrix[9],
		pairSumMatrix[6],pairSumMatrix[7],pairSumMatrix[8],pairSumMatrix[9],outfile54,4);
		//
	for (i=4; i<8; i++)
	{
		staticRR_result[5*8 + i] = 0.0;
		for (j=0; j<5; j++)
		{
			staticRR_result[5*8+i]+= staticRR_result[j*8+i];
		}
		staticRR_result[5*8 + i] /=5;
		staticRR_result[5*8 + i-4] = 100.0*staticRR_result[5*8 + i]/Posture_num;
	}

	for (i=0; i<6; i++)
	{
		for (j=0; j<8; j++)
		{
			outfile<<staticRR_result[i*8+j]<<",";
		}
		outfile<<endl;
	}

	outfile50.close();
	outfile51.close();
	outfile52.close();
	outfile53.close();
	outfile54.close();

		//Output an example matrix of 0X
	ofstream matrix01; 
	ofstream matrix02; 
	ofstream matrix03; 
	ofstream matrix04; 
	matrix01.open("D:\\iCode\\SignLanKinectCode\\staticRR\\distanceMatrix0x\\01.csv",ios::out); 
	matrix02.open("D:\\iCode\\SignLanKinectCode\\staticRR\\distanceMatrix0x\\02.csv",ios::out); 
	matrix03.open("D:\\iCode\\SignLanKinectCode\\staticRR\\distanceMatrix0x\\03.csv",ios::out); 
	matrix04.open("D:\\iCode\\SignLanKinectCode\\staticRR\\distanceMatrix0x\\04.csv",ios::out); 

	for (i=0; i<Posture_num; i++)
	{
		for (j=0; j<Posture_num; j++)
		{
			matrix01<<*(lastDistanceMatrix[10]+i*Posture_num+j)<<",";
			matrix02<<*(lastDistanceMatrix[11]+i*Posture_num+j)<<",";
			matrix03<<*(lastDistanceMatrix[13]+i*Posture_num+j)<<",";
			matrix04<<*(lastDistanceMatrix[16]+i*Posture_num+j)<<",";
		}
		matrix01<<endl;
		matrix02<<endl;
		matrix03<<endl;
		matrix04<<endl;
	}
	matrix01.close();
	matrix02.close();
	matrix03.close();
	matrix04.close();


	cout<<"-----------------"<<endl<<"Result"<<endl;
	for (i=0; i<6; i++)
	{
		if (i<5)
		{
			cout<<"Probe: P5"<<i<<endl;
		}
		else
		{
			cout<<"Average:"<<endl;
		}

		cout<<"Rank 1"<<'\t'<<staticRR_result[i*8+0]<<"\%"<<endl;
		cout<<"Rank 3"<<'\t'<<staticRR_result[i*8+1]<<"\%"<<endl;
		cout<<"Rank 5"<<'\t'<<staticRR_result[i*8+2]<<"\%"<<endl;
		cout<<"Rank 10"<<'\t'<<staticRR_result[i*8+3]<<"\%"<<endl;
		cout<<endl;
	}

		//Close and release
	infile.close();
	infileMask.close();
	outfile.close();
	for (i=0; i<20; i++)
	{
		delete[] lastDistanceMatrix[i];
	}

	cout<<"Done!"<<endl;
	getchar();
	return 0;
}

