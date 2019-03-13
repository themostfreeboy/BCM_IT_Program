#include <stdio.h>//用于printf和perror
#include <stdlib.h>//用于system
#include <string.h>//用于strlen
//#include <stdbool.h>//用于bool
//#include <memory.h>//用于memset
#include <stdarg.h>//用于va_list
#include <vector>//用于vector
#include <assert.h>//用于assert
#include <algorithm>//用于swap

using namespace std;//用于vector和swap

static FILE *fp = NULL;//日志文件指针

bool log_init()//创建打开日志文件
{
	fp = fopen("log.txt","w");
	if(!fp)	return false;
	return true;
}

void log(const char* pszFmt, ...)//写日志
{
	assert(fp);
	va_list args;
    va_start(args,pszFmt);
	vfprintf(fp,pszFmt,args);
	va_end(args);
}

void log_close()//关闭日志文件
{
	assert(fp);
	fclose(fp);
}

static unsigned char GFadd(unsigned char a, unsigned char b)//GF(2^4)加法
{
	assert(((a&0xf0)==0) && ((b&0xf0)==0));
	return a ^ b;
}

static unsigned char GFmul(unsigned char a, unsigned char b)//GF(2^4)乘法
{
	assert(((a&0xf0)==0) && ((b&0xf0)==0));
    unsigned char result = 0;
	int i;
    if((b&1) == 1)	result = a;
    b >>= 1;
    for(i = 1; i < 4; i ++)
	{
        if(a > 7)
		{
            a = ((a << 1) & 0x0f) ^ 0x03;
        }
        else
		{
            a <<= 1;
			a &= 0x0f;
        }
        if((b&1) == 1)
		{
            result ^= a;
        }
        b >>= 1;
    }
    return result;
}

static vector<vector<unsigned char>> GFMatAdd(vector<vector<unsigned char>>& a, vector<vector<unsigned char>>& b)//GF(2^4)域上的矩阵加法
{
	assert(a.size() == b.size());
	unsigned int i,j;
	vector<vector<unsigned char>> result(a.size());
	for(i=0;i<a.size();i++)
	{
		result[i].resize(a[0].size());
		for(j=0;j<a[0].size();j++)
		{
			result[i][j]=(a[i][j]^b[i][j]) & 0x0f;
		}
	}
	return result;
}

static vector<vector<unsigned char>> GFMatMul(vector<vector<unsigned char>>& a, vector<vector<unsigned char>>& b)//GF(2^4)域上的矩阵乘法
{
	assert(a.size()== b[0].size() && a[0].size()==b.size());
	unsigned int i,j,k;
	unsigned char sum;
	vector<vector<unsigned char>> result(a.size());
	for(i=0;i<a.size();i++)
	{
		result[i].resize(b[0].size());
		for(j=0;j<b[0].size();j++)
		{
			sum = 0;
			for(k=0;k<a[0].size();k++)
			{
				sum ^= GFmul(a[i][k],b[k][j]);
			}
			result[i][j] = sum;
		}
	}
	return result;
}

static unsigned char sbox_inv[16];//存放逆元

static void calSbox_inv()//计算逆元
{
	int i,j;
	sbox_inv[0] = 0;
	for(i=1;i<16;i++)
	{
		for(j=1;j<16;j++)
		{
			if(GFmul(i,j)==1)
			{
				sbox_inv[i] = j;
				break;
			}
		}
	}
}

static unsigned char SBoxValue(unsigned char x)//通过矩阵乘法计算出S盒里具体的值
{
	assert((x&0xf0)==0);
    bool xb[4];
    unsigned char y = sbox_inv[x];
    const bool N[4][4] = {1, 0, 0, 0,
                          1, 1, 0, 0,
                          1, 1, 1, 1,
                          0, 1, 1, 1};
    const bool C[4] = {1, 0, 0, 1};
	int i,j;
    for(i=0;i<4;i++)
	{
        xb[i] = (y&1);
        y >>= 1;
    }
    bool temp[4];
    memset(temp,0,4);
    for(i=0;i<4;i++)
	{
        for(j=0;j<4;j++)
		{
            temp[i] ^= (N[i][j] & xb[j]);
        }
        temp[i] ^= C[i];
    }
    unsigned char result = 0;
    result |= (unsigned char)temp[3];
    for(i=2;i>=0;i--)
	{
        result <<= 1;
		result &= 0x0f;
        if(temp[i])	result |= 1;
    }
    return result;
}

static unsigned char SBox[4][4];//s盒

void calSBox()//计算s盒
{
	int i,j;
	unsigned char temp;
	calSbox_inv();
	for(i=0;i<4;i++)
	{
        for(j=0;j<4;j++)
		{
            temp = i*4 + j;
            SBox[i][j] = SBoxValue(temp);
        }
    }
}

static void ShiftRows(vector<vector<unsigned char>>& A)//行移动
{
	assert(A.size()==2);
	assert(A[0].size()==2);
	swap(A[1][0],A[1][1]);
}

static vector<vector<unsigned char>> MixMat;//用于列混淆时的矩阵

void initMixMat()//计算MixMat矩阵内的值
{
	MixMat.resize(2);
	MixMat[0].resize(2);
	MixMat[1].resize(2);
	MixMat[0][0] = 0x03;
	MixMat[0][1] = 0x07;
	MixMat[1][0] = 0x04;
	MixMat[1][1] = 0x03;
}

static vector<vector<unsigned char>> MixColumns(vector<vector<unsigned char>>& B)//列混淆
{
	assert(B.size()==2);
	assert(B[0].size()==2);
	return GFMatMul(MixMat,B);
}

static unsigned char SubBytes(unsigned char x)//返回S盒中对应的值
{
	assert((x&0xf0)==0);
	return SBox[x/4][x%4];
}

static const unsigned char RC[6] = {0x00, 0x03, 0x06, 0x0c, 0x0b, 0x05};//存放RCi(RC[0]无用)

static inline unsigned char L(unsigned char x)//返回L左4位
{
	return (x>>4)&0x0f;
}

static inline unsigned char R(unsigned char x)//返回R右4位
{
	return x&0x0f;
}

static vector<vector<vector<unsigned char>>> MultRoundKey(const unsigned char K[4])//多轮秘钥处理
{
	unsigned char W0=K[0],W1=K[1],W2=K[2],W3=K[3];
	unsigned char W4,W5,W6,W7;
	int i;
	unsigned char T;
	vector<vector<vector<unsigned char>>> resultK(6);
	resultK[0].resize(2);
	resultK[0][0].resize(2);
	resultK[0][1].resize(2);
	resultK[0][0][0] = GFadd(GFadd(GFmul(L(W0),R(W0)),L(W0)),R(W0));
	resultK[0][1][0] = GFadd(GFadd(GFmul(L(W1),R(W1)),L(W1)),R(W1));
	resultK[0][0][1] = GFadd(GFadd(GFmul(L(W2),R(W2)),L(W2)),R(W2));
	resultK[0][1][1] = GFadd(GFadd(GFmul(L(W3),R(W3)),L(W3)),R(W3));
	for(i=1;i<=5;i++)//Round 1-Round 5
	{
		T = (W3<<3) | ((W3>>5) & 0x07);
		T = (SubBytes(L(T))<<4) | SubBytes(R(T));
		T = T ^ RC[i];
		W4 = W0 ^ T;
		W5 = W1 ^ W4;
		W6 = W2 ^ W5;
		W7 = W3 ^ W6;
		resultK[i].resize(2);
		resultK[i][0].resize(2);
		resultK[i][1].resize(2);
		resultK[i][0][0] = GFadd(GFadd(GFmul(L(W4),R(W4)),L(W4)),R(W4));
		resultK[i][1][0] = GFadd(GFadd(GFmul(L(W5),R(W5)),L(W5)),R(W5));
		resultK[i][0][1] = GFadd(GFadd(GFmul(L(W6),R(W6)),L(W6)),R(W6));
		resultK[i][1][1] = GFadd(GFadd(GFmul(L(W7),R(W7)),L(W7)),R(W7));
		W0 = W4;
		W1 = W5;
		W2 = W6;
		W3 = W7;
	}
	return resultK;
}

static void calEk(const unsigned char in[4],unsigned char out[4],const unsigned char K_hex[4])//计算out=Ek(in)
{
	unsigned short L0,R0,L1,R1;
	int i,j;
	vector<vector<vector<unsigned char>>> key;
	vector<vector<unsigned char>> mat1(2);
	vector<vector<unsigned char>> mat2(2);
	vector<vector<unsigned char>> mat3;
	vector<vector<unsigned char>> mat4;
	mat1[0].resize(2);
	mat1[1].resize(2);
	mat2[0].resize(2);
	mat2[1].resize(2);
	key = MultRoundKey(K_hex);
	L0 = ((unsigned short)in[0]<<8) | in[1];
	R0 = ((unsigned short)in[2]<<8) | in[3];
	for(i=0;i<=5;i++)//Round 0-Round 5
	{
		//log输出中间结果：每轮的L0与R0
		log("Round %d:L%d=",i,i);
		for(j=0;j<8;j++)
		{
			log("%c",((L0>>(7-j))&0x01)+'0');
		}
		log(",R%d=",i);
		for(j=0;j<8;j++)
		{
			log("%c",((R0>>(7-j))&0x01)+'0');
		}
		log("\n");

		mat1[0][0] = (R0>>12) & 0x0f;
		mat1[1][0] = (R0>>8) & 0x0f;
		mat1[0][1] = (R0>>4) & 0x0f;
		mat1[1][1] = R0 & 0x0f;
		mat2[0][0] = SubBytes(mat1[0][0]);
		mat2[0][1] = SubBytes(mat1[0][1]);
		mat2[1][0] = SubBytes(mat1[1][0]);
		mat2[1][1] = SubBytes(mat1[1][1]);
		mat3 = GFMatMul(key[i],mat2);
		mat4 = MixColumns(mat3);
		ShiftRows(mat4);
		L1 = R0;
		R1 = L0 ^ (((unsigned short)mat4[0][0]<<12)|((unsigned short)mat4[1][0]<<8)|((unsigned short)mat4[0][1]<<4)|((unsigned short)mat4[1][1]));
		L0 = L1;
		R0 = R1;
	}
	out[0] = R0>>8;
	out[1] = R0 & 0xff;
	out[2] = L0>>8;
	out[3] = L0 & 0xff;
}

static void binstr2Hex(const char* binstr, unsigned char* hex)//二进制字符串转十六进制
{
	int n = strlen(binstr),i,j;
	assert(n%32==0);
	unsigned char temp;
	for(i=0;i<n/8;i++)
	{
		temp = 0;
		for(j=0;j<8;j++)
		{
			temp <<= 1;
			temp |= (binstr[8*i+j] - '0');
		}
		hex[i] = temp;
	}
}

static void hex2Binstr(const unsigned char* hex, int hex_size, char* binstr)//十六进制转二进制字符串
{
	assert(hex_size%4==0);
	int i,j;
	for(i=0;i<hex_size;i++)
	{
		for(j=0;j<8;j++)
		{
			binstr[8*i+j] = ((hex[i]>>(7-j))&(0x01)) + '0';
		}
	}
	binstr[8*hex_size] = '\0';
}

void cipher(const char M[], const char K[33], const char IV[33], char C[])//加密函数
{
	assert(strlen(M)%32==0);
	assert(strlen(K)==32);
	assert(strlen(IV)==32);
	printf("M=%s\nK=%s\nIV=%s\n",M,K,IV);
	log("M=%s\nK=%s\nIV=%s\n",M,K,IV);
	int M_hex_size = strlen(M)/8;
	unsigned char* M_hex = (unsigned char*)malloc(M_hex_size*sizeof(unsigned char*));
	unsigned char K_hex[4];
	unsigned char IV_hex[4];
	unsigned char* C_hex = (unsigned char*)malloc(M_hex_size*sizeof(unsigned char*));
	binstr2Hex(M,M_hex);
	binstr2Hex(K,K_hex);
	binstr2Hex(IV,IV_hex);
	int i,j;
	unsigned char temp_in[4],temp_out[4],temp_M[4];
	unsigned int i_temp_C;
	temp_in[0] = IV_hex[0];
	temp_in[1] = IV_hex[1];
	temp_in[2] = IV_hex[2];
	temp_in[3] = IV_hex[3];
	temp_M[0] = M_hex[0];
	temp_M[1] = M_hex[1];
	temp_M[2] = M_hex[2];
	temp_M[3] = M_hex[3];
	for(i=0;i<M_hex_size/4;i++)
	{
		log("Group %d:\n",i+1);
		calEk((const unsigned char*)temp_in,temp_out,(const unsigned char*)K_hex);
		i_temp_C = 0;
		for(j=0;j<4;j++)
		{
			i_temp_C <<= 8;
			i_temp_C |= (temp_out[j] ^ temp_M[j]);
		}
		C_hex[4*i] = (i_temp_C>>24) & 0xff;
		C_hex[4*i+1] = (i_temp_C>>16) & 0xff;
		C_hex[4*i+2] = (i_temp_C>>8) & 0xff;
		C_hex[4*i+3] = i_temp_C & 0xff;
		temp_in[0] = C_hex[4*i];
		temp_in[1] = C_hex[4*i+1];
		temp_in[2] = C_hex[4*i+2];
		temp_in[3] = C_hex[4*i+3];
		temp_M[0] = M_hex[4*(i+1)];
		temp_M[1] = M_hex[4*(i+1)+1];
		temp_M[2] = M_hex[4*(i+1)+2];
		temp_M[3] = M_hex[4*(i+1)+3];
	}
	hex2Binstr(C_hex,M_hex_size,C);
	printf("C=%s\n\n",C);
	log("C=%s\n\n",C);
	free(M_hex);
	free(C_hex);
}

int main()
{
	if(!log_init())
	{
		perror("日志文件创建打开失败\n");
		system("pause");
		return 0;
	}
	calSBox();//计算S盒
	initMixMat();//计算MixMat矩阵内的值
	char C[161];//存储加密后数据的buffer(注意此buffer大小)

	//cipher("101100101111011010110001001001110110100110100100100000110100000111100100000100100011110001010110","10000001100001100110011010100011","11110000101010001011000100001001",C);//debug(1)
	//cipher("100101001011100110010011101010101000110000010110010100010011010000101000011101100111011000111100","01101100010101001000110010001111","11110101100101000001111101100001",C);//debug(2)
	//cipher("001001100011100000100001110010100011101011101011100000100000001001000001111011000000111110000100","00100011011111001110010000101110","11000011000000001101000100011011",C);//debug(3)

	cipher("101001111100110101100110001101000010110010000010011011011000101100101011110100101110010000010010","01100100011010001111110101101110","01101100000011011111000000110010",C);//(a)
	cipher("110011000001101010001001010110010000100000100110001100101000001001010001000010010111001100110000","01001101010010100010110110111110","10110100101111110110111110100111",C);//(b)
	cipher("000010111101000111100011011001000010011000101100010101010110010000011000110111011010000011001001","01000110111001000110110010110000","11011111010101110111111011000010",C);//(c)
	cipher("11110101101000010100101110101011100000001111000000001001100010001010011111011110100111110100110011001100010001010000110010111010","11001010110011100001100101101001","11100000111000001101010010101101",C);//(d)
	cipher("11011001011000001000100111000101001101100100000010101100010011001110111100011010001011100110110110101110011011011001010000100110","00001001001001000110011010001111","01011100011111011100001110000000",C);//(e)
	cipher("11000001111110110100000111000010101111011001101100001110110011011011111000111101111011011111110001111001100010011100100011101110","10101101110000011001011001011011","01100110000100111011101001000110",C);//(f)
	cipher("0110011011011100111001000011011101100001111000001001001001000100000100110111001010001101100100001100001100101110000010101001010000111101011010110010010100101001","10000011011001000101001001110011","00100011010101000000111000001110",C);//(g)
	cipher("0100000011000001101110010000010000101111000101001001010010111001100000010011100010101100000000100011110101101101100001110101010111010010100101100011110011110101","00001010010111000101000010010100","00011111100100011101010001100100",C);//(h)
	log_close();
	system("pause");
	return 0;
}