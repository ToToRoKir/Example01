
const NRule=30;  // ���ᨬ��쭮� 稫� �ࠢ�� ��� ������ ���ନ����
const CNRule=50; // ��饥 �᫮ ⠪�� ���ନ�����
const NLenStr=80; // ����� �ࠢ��� � �������� ���ନ����

// ᫥���騥 2 ����⠭�� �ᯮ������� ����ᮬ SetStr ����� ������ ��
// ��ப ������⢮
const NSet=30; // <- ����. �᫮ ��ப
const NChar=40; // <- ����. ����� ����� ��ப�

extern void HP();

//--------------------------------------------------------------------------
// ����� ��ꥪ⮢ ��� ࠡ��� � ��ப��� (� ������⢮�)
// (�ᯮ����⥫�� ������)
//--------------------------------------------------------------------------


// Class SetStr ------------------------------------------------------------
//typedef  char TElem[NChar];	// ��ப�
//typedef  TElem TSet[NSet];	// ������ ��ப

class SetStr{
protected:
   char		MSet[NSet][NChar];	// ������ ��ப (������⢮)
   int		RElem;  // ��᫮ ������⮢ � ⠡���
   int		itmpRElem;  // �஬������ ����� ������� � ⠡���

public:
   SetStr(){RElem = 0;}; // ���������
   ~SetStr();            // ��������
   int Is(char *el);     // ��楤�� �஢������� ������⢨� � ⠡��� MSet
			 // ��ப� el
   int AddElem(char *el);// �������� � ⠡���� ������� el
   void InitStack(){itmpRElem=-1;};        // ���樨��� itmpRElem;
   char *RetElem()       // �����頥� ��� ᫥���騩 �������
			 // ��� (�᫨ ��� �����稫���) NULL
     { itmpRElem+=1;
       if (itmpRElem<RElem)
	 {return MSet[itmpRElem];}
       else
	{return NULL;}
     };
   void InitSet(){RElem = 0;};	  // ���樠������� RElem

   int  operator ==(SetStr Set1); // �ࠢ������ 2 ������⢠
   int  operator ==(SetStr *Set1); // �ࠢ������ 2 ������⢠
   int  Comparation(SetStr *Set1);//�ࠢ���� ������⢮ this � ������⢮� Set1

   void operator  =(SetStr Set1); // ��᢮���� �������
   void operator  =(SetStr *Set1); // ��᢮���� �������
   void Appropriation(SetStr *Set1);//��᢮��� �������� this ������⢮ Set1

};
// End Class SetStr --------------------------------------------------------


// Class SetOfSet ------------------------------------------------------------
struct TSSet {        // ������ ⠡���
   char         NameClass[NChar];
   SetStr 	ListOfClass;
 };

class SetOfSet{
protected:
   TSSet	*pList[NSet];	// ���᮪ ⠡��� (������⢮)
   int		RElem;  	// ��᫮ ������⮢ � ⠡���
   int		itmpRElem;  	// �஬������ ����� ������� � ⠡���

public:
   SetOfSet(){pList[0]=NULL;RElem = 0;itmpRElem=0;} // ���������
   ~SetOfSet();         			    // ��������
   int IsElem(char *ClassOfElem,char *Elem);
	// ��楤�� �஢������� ������⢨� � ����� ClassOfElem
	// ��ப� el
   int IsClass(char *ClassOfElem);
	// ��楤�� �஢������� ������⢨� ����� ClassOfElem
   int AddElem(char *ClassOfElem,char *Elem);
	// �������� � ����� ClassOfElem ������� el. �᫨ ⠪��� �����
	// ��� � ��楤�� ��� ᮧ����.
   void InitStack(){itmpRElem=-1;}// ���樨��� itmpRElem
   char *RetClass()	 // �����頥� ��� ᫥���騩 �����
			 // ��� (�᫨ ��� �����稫���) NULL
     { itmpRElem+=1;
       if (itmpRElem<RElem)
	 {pList[itmpRElem]->ListOfClass.InitStack();
	  return pList[itmpRElem]->NameClass;}
       else
	{return NULL;}
     };

   char *RetElemOfClass()// �����頥� ��� ᫥���騩 ������� �����
			 // ��।�������� RetClass ��� (�᫨ ��� �����稫���)
			 // NULL
     { if (itmpRElem<RElem)
	 {return pList[itmpRElem]->ListOfClass.RetElem();}
       else
	{return NULL;}
     };
};

// End Class SetOfSet --------------------------------------------------------

//--------------------------------------------------------------------------
// ����� ��ꥪ⮢ ��� �࠭���� �ࠢ�� �ࠬ��⨪�
//--------------------------------------------------------------------------
typedef  char vc_StrRuls[NLenStr];

struct Ruls{ // ������� ��� �࠭���� �ࠢ�� �ࠬ��⨪�
 char NoTerm[NLenStr]; // �������� ���ନ���� � ���஬� �⭮����� �ࠢ���
 vc_StrRuls Rule[NRule]; // �ࠢ��� �ࠬ��⨪�
		    // �� ���ᨬ��쭮� �᫮ ��।������ NRule
 int   RealR; // �᫮ �ࠢ�� ��� ������� ���ନ����
};

typedef  Ruls *ArRuls[CNRule];


class StructRuls {
protected:
//---------------------
  ArRuls  TablRuls; // ������ �ࠢ�� ��� ���ନ����� (� ���� ����ᥩ
		    // ⨯� Ruls)
		    // ���ᨬ��쭮� �᫮ ���ନ����� CNRule
  int	  RealRuls; // �᫮ ���ନ����� ��� ������ �ࠬ��⨪�
  int     vn_NomerNoTerm; // ��� ��ॡ�� ���ନ�����
  SetStr  ar_SetN;  // ������⢮ ���ନ�����(� �ࠬ��⨪�� ������砥��� N)
  SetStr  ar_SetE;  // ������⢮ �ନ����� ��� ��䠢��
		    // (� �ࠬ��⨪�� ������砥��� E)
  SetStr  ar_SetN1; // �஬����筮� ������⢮ ���ନ�����
  SetStr  ar_SetE1; // �஬����筮� ������⢮ �ନ�����
  char    vc_StartNoTerm[256]; // ��砫�� ���ନ��� �ࠬ��⨪�
//---------------------

public:

  StructRuls(){InitRuls();
	    vn_NomerNoTerm=0;};  	// ���������
  int NumberNoTerm(char *Name); 	// �� ����� ���ନ���� Name ����
					// ��� ����� � ⠡��� ���ନ�����
					// TablRuls
  void InitRuls(); 		        // ���樠������� ⠡���� NULL-��
  int AddRuls(Ruls * Rl); 	        // �������� ���� ���ନ��� � ⠡�.
					// �� ������ ⨯� Ruls
  int AddRul(char * NoTerm,char * Rl);  // �������� ����� �ࠢ��� � ⠡�.
					// ��� ���ନ���� NoTerm
  int DeleteRule(char *NoTerm,int vn_Number);
	// ������� �ࠢ��� vn_Number � ���ନ���� NoTerm
  char *ReturnRule(char *NoTerm,int Nr);// �� �������� ���ନ���� NoTerm �
					// ������ �ࠢ��� �����頥� �ࠢ���
  int ReturnRealR(char *NoTerm);        // �����頥� �� ������ ���ନ����
					// �᫮ �ࠢ�� ��� ����
  char NextSymbol(char *&vc_StrInput, char *vc_Symbol);
  void InitNoTermAndTerm();			// ���樠������� ������⢮
	// ���ନ������ ᨬ�����
	// ������� �� �ࠢ��� � �� ���ନ���� �������� � ���
	// ��쥤������� � ������⢮ ar_SetN, � �� �ନ���� � ar_SetT

  int Algoritm_IsGammaticEmpty(); 	// �஢���� ���� �� �ࠬ��⨪�
      // ������ �᭮��� �� �८�ࠧ������ �ࠬ��⨪� ���ᠭ��� � �����
      // �.��, ��.��쬠� ����� ᨭ⠪��᪨�� �������, ��ॢ��� �
      // �������樨 ��� 1 ���⠪��᪨� ������  ���. 169

  int Algoritm_DelNonSymbol();// �������� �����⨦���� ᨬ�����
      // ������ �᭮��� �� �८�ࠧ������ �ࠬ��⨪� ���ᠭ��� � �����
      // �.��, ��.��쬠� ����� ᨭ⠪��᪨�� �������, ��ॢ��� �
      // �������樨 ��� 1 ���⠪��᪨� ������  ���. 171

  int Algoritm_DelReduceRules();// ������ ���� �� ����� ४����
      // ������ �᭮��� �� ������ ����஢�
      // 1) ��室����� �� �ࠢ��� � ������ � �ࠢ�� ��� ���� �⮨� �ନ���
      // 2) ��⥬ ��室����� �� ���ନ���� � ������ �� ��� �ࠢ���� � �ࠢ��
      //    ��� ���� �⮨� �ନ���
      // 3) ��⥬ ��������� 蠣 2 ���� Ni_<>Ni-1
      // (��� Ni_-������⢮ ��ନ஢���� �� i-�� �ண��� ��쥤������� �
      // ������⢮� Ni-1; Ni_ e (Ni U Ni-1) )
      // �����頥� 1 �᫨ �� ��ଠ�쭮 � 2 �᫨ ���� ४����

  void ShowRuls();			// ��ᯥ���� �� �ࠢ���
  void DeleteRuls();                    // ������� ��� ⠡����
  int LoadRuls(char *FileN);            // ����� ⠡���� � ��᪠
  int SaveRuls(char *FileN);            // ������� ⠡���� �� ���
  ~StructRuls(){DeleteRuls();};  	// ��������

};//End StructRuls ----------------------------------------------------------


  int fReadLn(FILE *pOf)
     {int  i=0;

       if (pOf!=NULL)
	 { while (fscanf(pOf,"%c",&MBuffer[i]) && !feof(pOf) && (MBuffer[i]!='\n'))
		 {i++;}
	   if (MBuffer[i]=='\n')
	    {MBuffer[i]='\0';
	     return 1;}
	   else
	    {if (feof(pOf)) {return 0;}
	     else { return -1;}}
	 }
       else
	 {return -1;}
     }

// Class SetStr
//---------------------------------------------------------------------------
   SetStr::~SetStr()
      {
//        register int i=0;
//	for(i=0;i<RElem;i++)
//	 {delete [] MSet[i];
//	  printf("SetStr delete MSet[%d] : \n",i);
//	  HP();}
      };

   int SetStr::Is(char *el)// ��楤�� �஢������� ������⢨� � ⠡��� MSet
	// ��ப� el
      { register int i=-1,pf;
	do{
	 i++;
	 pf = strcmp(MSet[i],el);
	}while((pf!=0)&&(i<RElem));
	if ((pf==0) && (i<RElem))
	 {return 1;}
	else
	 {return 0;}
      }

   int SetStr::AddElem(char *el)	// �������� � ⠡���� ������� el
      {if (RElem<CNRule)
	 {if (! this->Is(el))
	   { strcpy(MSet[RElem],el);
	     RElem++;}  }
       else
	 {return 0;}
       return 1;
      }


   int SetStr::operator ==(SetStr Set1) // �ࠢ������ 2 ������⢠
     {
      char *pc_SymbolA=NULL;  // � �᫨ ��� ᮢ������ � �뤠�� 1 ���� 0
      int   vl_Equal;

      this->InitStack();
      vl_Equal=1;
      pc_SymbolA = this->RetElem();
      while((pc_SymbolA) && (vl_Equal) )
	{ vl_Equal = Set1.Is(pc_SymbolA) ;
	  pc_SymbolA = this->RetElem();	}

      return vl_Equal;
     };

   int SetStr::operator ==(SetStr *Set1) // �ࠢ������ 2 ������⢠
     {
      char *pc_SymbolA=NULL;  // � �᫨ ��� ᮢ������ � �뤠�� 1 ���� 0
      int   vl_Equal;

      this->InitStack();
      vl_Equal=1;
      pc_SymbolA = this->RetElem();
      while((pc_SymbolA) && (vl_Equal) )
	{ vl_Equal = Set1->Is(pc_SymbolA) ;
	  pc_SymbolA = this->RetElem();	}

      return vl_Equal;
     };

   void SetStr::operator =(SetStr Set1) // ��᢮���� �������
     {char *pc_SymbolA=NULL;

      Set1.InitStack();
      pc_SymbolA = Set1.RetElem();
      this->InitSet();
      while( pc_SymbolA )
	{this->AddElem(pc_SymbolA);
	 pc_SymbolA = Set1.RetElem();}

     };

   void SetStr::operator =(SetStr *Set1) // ��᢮���� �������
     {char *pc_SymbolA=NULL;

      Set1->InitStack();
      pc_SymbolA = Set1->RetElem();
      this->InitSet();
      while( pc_SymbolA )
	{this->AddElem(pc_SymbolA);
	 pc_SymbolA = Set1->RetElem();}

     };

   int SetStr::Comparation(SetStr *Set1)//�ࠢ���� ������⢮ this � ������⢮� Set1
     {
      char *pc_SymbolA=NULL;  // � �᫨ ��� ᮢ������ � �뤠�� 1 ���� 0
      int   vl_Equal;

      this->InitStack();
      vl_Equal=1;
      pc_SymbolA = this->RetElem();
      while((pc_SymbolA) && (vl_Equal) )
	{ vl_Equal = Set1->Is(pc_SymbolA) ;
	  pc_SymbolA = this->RetElem();	}

      return vl_Equal;
     };

   void SetStr::Appropriation(SetStr *Set1)//��᢮��� �������� this ������⢮ Set1
     {
      char *pc_SymbolA=NULL;

      Set1->InitStack();
      pc_SymbolA = Set1->RetElem();
      this->InitSet();
      while( pc_SymbolA )
	{this->AddElem(pc_SymbolA);
	 pc_SymbolA = Set1->RetElem();}
     };

// End of Class StrSet
//---------------------------------------------------------------------------


// Class SetOfSet
//---------------------------------------------------------------------------
   SetOfSet::~SetOfSet()
   {register int i=0;

    for(i=0; i<RElem; i++)
     {//pList[i]->ListOfClass.~SetOfSet();
      delete pList[i];
      pList[i] = NULL;
     }
   };

   int SetOfSet::IsElem(char *ClassOfElem,char *Elem)
	   // ��楤�� �஢������� ������⢨� � ����� ClassOfElem
	   // ��ப� el
   { register int i=0,pf=1;

     while((pf!=0)&&(pList[i]!=NULL)&&(i<RElem)){
       pf = strcmp(pList[i]->NameClass,ClassOfElem);
       i++;
      };
     if (pf==0)
      {return pList[i-1]->ListOfClass.Is(Elem);}
     else
      {return 0;}
   }

   int SetOfSet::IsClass(char *ClassOfElem)
	   // ��楤�� �஢������� ������⢨� ����� ClassOfElem
   { register int i=0,pf=1;

     while((pf!=0)&&(pList[i]!=NULL)&&(i<RElem)){
       pf = strcmp(pList[i]->NameClass,ClassOfElem);
       i++;
      };
     if (pf==0)
      {return 1;}
     else
      {return 0;}
   }

   int SetOfSet::AddElem(char *ClassOfElem,char *Elem)
	   // �������� � ����� ClassOfElem ������� el. �᫨ ⠪��� �����
	   // ��� � ��楤�� ��� ᮧ����.
   { register int i=0,pf=1;
     TSSet	*pntList=NULL;

     if (ClassOfElem != NULL)
      {if ( (! this->IsClass(ClassOfElem))&&(RElem<CNRule) )
	{//�᫨ ��� ⠪��� �����
	 pntList = new (TSSet);
	 strcpy(pntList->NameClass,ClassOfElem);
	 pntList->ListOfClass.AddElem(Elem);
	 pList[RElem]=pntList;
	 RElem++;
	}
       else
	{//�᫨ ⠪�� ���� �������
	 i=0;
	 pf=1;
	 while((pf!=0)&&(pList[i]!=NULL)&&(i<RElem)){
	   pf = strcmp(pList[i]->NameClass,ClassOfElem);
	   i++;
	  };
	 if (pf==0)
	  {return pList[i-1]->ListOfClass.AddElem(Elem);}
	}
       }
     else
      {return 0;}
     return 1;
   }
// Class StructRuls
//---------------------------------------------------------------------------

  int StructRuls::NumberNoTerm(char *Name)// �� ����� ���ନ���� Name ����
	// ��� ����� � ⠡��� ���ନ����� TablRuls
      {
       register i=-1,j=1;

       if (Name!=NULL)
	{do {
	 i +=1;
	 j = strcmp(TablRuls[i]->NoTerm,Name);
	 }while((TablRuls[i] != NULL) && (j != 0));
	 if (strcmp(TablRuls[i]->NoTerm,Name)==0)
	  {return i;} }
       return -1;
      }


  void StructRuls::InitRuls()// ���樠������� ⠡���� NULL-��
     {
      register i,j;
      for (i=0;i<CNRule;i++)
       {TablRuls[i] = NULL;}

      RealRuls = 0;
     }

  int StructRuls::AddRuls(Ruls * Rl)// �������� ���� ���ନ��� � ⠡�.
	// �� ������ ⨯� Ruls
    {
      if (RealRuls<CNRule)
       {TablRuls[RealRuls] = Rl;
	RealRuls +=1;}
      else
       {exit(1);}
      return 0;
    }

  int StructRuls::AddRul(char * NoTerm,char * Rl)// �������� ����� �ࠢ��� �
	// ⠡���� ��� ���ନ���� NoTerm
     {
      register i;

      i = NumberNoTerm(NoTerm);
      if ((i>=0) && (i<RealRuls) && (strcmp(TablRuls[i]->NoTerm,NoTerm)==0) )
       {
//        TablRuls[i]->Rule[TablRuls[i]->RealR] = new char[strlen(Rl)+1];
	strcpy(TablRuls[i]->Rule[TablRuls[i]->RealR],Rl);
	TablRuls[i]->Rule[TablRuls[i]->RealR][strlen(Rl)]='\0';
	TablRuls[i]->RealR +=1;}
      return 0;
     }

  int StructRuls::DeleteRule(char *NoTerm,int vn_Number)
      // ������� �ࠢ��� vn_Number � ���ନ���� NoTerm
     {
      register i,j;

      i = NumberNoTerm(NoTerm);
      if ((i>=0) && (i<RealRuls) && (strcmp(TablRuls[i]->NoTerm,NoTerm)==0) )
       { for (j=vn_Number; j<TablRuls[i]->RealR-1; j++)
	   {strcpy(TablRuls[i]->Rule[TablRuls[j]->RealR],TablRuls[i]->Rule[TablRuls[j+1]->RealR]);}
	 TablRuls[i]->RealR-=1;
       }

      return 0;
     }

  char *StructRuls::ReturnRule(char *NoTerm,int Nr)// �� �������� ���ନ����
	// NoTerm � ������ �ࠢ��� �����頥� �ࠢ��� ��� NULL �᫨
	// ⠪��� �ࠢ��� ���
     {
      register i;

      i = NumberNoTerm(NoTerm);
      if ((i == -1)||(i>RealRuls))
       {return NULL;}
      else
       if ((TablRuls[i]->RealR>Nr) && (Nr>=0))
	 {return TablRuls[i]->Rule[Nr];}
	else
	 {return NULL;}
     }

  int StructRuls::ReturnRealR(char *NoTerm)// �����頥� �� �������� ���ନ����
	// �᫮ �ࠢ�� ��� ����
     {
      register i;

      i = NumberNoTerm(NoTerm);
      if ((i == -1)||(i>RealRuls))
       {return -1;}
      else
       {return (TablRuls[i]->RealR);}
     }

  char StructRuls::NextSymbol(char *&vc_StrInput, char *vc_Symbol)
     // �뤠�� ᫥�. ������� ��ப� vc_StrInput �᫨ �� ���ନ���
     // � �뤠���� "N" ���� "T"
     {
      int  pT=1,pi=0;
      char vc_S;

      pi = 0;
      do{
	switch(vc_StrInput[pi]){
	case '\0': vc_StrInput=NULL; return 'E';break;
	case ' ': pi++; break;
	case '.': pi++; break;
	case ')': pi++; break;
	case '(': pi++; break;
	default :
	 vc_StrInput = &vc_StrInput[pi]; // ��⠭����� 㪠��⥫� �� ��砫�
	 pi = 0;                         // ᫥�. ᨬ����
	 do{                             // ����� ᨬ���
	   pi++;
	 }while((vc_StrInput[pi] != ')') && (vc_StrInput[pi] != ' ') && (vc_StrInput[pi] != '.'));
	 strncpy(vc_Symbol,vc_StrInput,pi); vc_Symbol[pi] = '\0';
	 vc_StrInput = &vc_StrInput[pi];
	 pT=0;
	 if (vc_Symbol[0]=='<')
	  vc_S = 'N';
	 else
	  vc_S = 'T';
	}
      }while(pT != 0);

      return vc_S;
     }

  void StructRuls::InitNoTermAndTerm()	// ���樠������� ������⢮
	// ���ନ������ ᨬ�����
	// ������� �� �ࠢ��� � �� ���ନ���� �������� � ���
	// ��쥤������� � ������⢮ ar_SetN, � �� �ନ���� � ar_SetT
     {char *vp_point=NULL;
      char vc_Symbol[256];
      char vc_S;
      int  i=0,j=0;

      for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
       { for (j=0;j<TablRuls[i]->RealR;j++)//��ॡ�� ��� �ࠢ�� � ������ ��.
	  { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	    while(vp_point)
	     {vc_S = this->NextSymbol(vp_point,vc_Symbol);//�뤥���� ᫥�.
							  // ᬢ�� � �ࠢ���
	      if (vc_S=='N')// �᫨ �� ���ନ���
		{ar_SetN.AddElem(vc_Symbol);}
	      else  // �᫨ �� �ନ���
		{if (vc_S =='T')
		   ar_SetE.AddElem(vc_Symbol);} }
	  }
       }
     }


  int StructRuls::Algoritm_IsGammaticEmpty()// �஢���� ���� �� �ࠬ��⨪�
      // ������ �᭮��� �� �८�ࠧ������ �ࠬ��⨪� ���ᠭ��� � �����
      // �.��, ��.��쬠� ����� ᨭ⠪��᪨�� �������, ��ॢ��� �
      // �������樨 ��� 1 ���⠪��᪨� ������  ���. 169
     {
      SetStr *ar_SetNi=NULL,*ar_SetNi_1=NULL;
      int i=0,j=0,vl_Is=0,vn_RetCase=0;
      char *vp_point=NULL,vc_S,vc_Symbol[256];

      ar_SetNi = new SetStr();
      ar_SetNi_1 = new SetStr();
      do{
	 ar_SetNi_1->Appropriation(ar_SetNi);
//	 ar_SetNi_1=ar_SetNi;
	 for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
	 // ����� ����� �᪮��� ��� ��楤��� �᫨ �� �஢����� ���ନ����
	 // ����� 㦥 �ਭ������� ar_SetNi_1
	  {for (j=0;j<TablRuls[i]->RealR;j++)//��ॡ�� ��� �ࠢ�� � ������ ��.
	    { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// �ய�����
	      // ���� ���ନ��� ⠪ ��� �ࠢ��� ��稭����� �
	      // ���樠�������饣� ���ନ���� � ��� �� �ய�᪠��

	      // �᫨ �ࠢ��� 㤮���⢮��� �᫮���
	      // {A | (A->a �ਭ������� P) � ��ப�-a �ਭ��. (N(i-1)UE)*} �
	      // ��쥤����� ���ନ��� � ���. ��稭����� ������ �ࠢ��� (A)
	      // � ar_SetNi
	      vl_Is=1;
	      while((vp_point) && (vl_Is))
	       {vc_S = this->NextSymbol(vp_point,vc_Symbol);//�뤥���� ᫥�.
							    // ᬢ�� � �ࠢ���
		if (vc_S=='N')// �᫨ �� ���ନ���
		  {vl_Is=ar_SetNi_1->Is(vc_Symbol);}
		else  // �᫨ �� �ନ���
		  {if (vc_S =='T')
		     vl_Is=ar_SetE.Is(vc_Symbol);} }
	      if (vl_Is)// �᫨ ��. �᫮��� (��. ��� �)
	       {ar_SetNi->AddElem(TablRuls[i]->NoTerm);}// ������塞 ���ନ���
	    }
	  }
//      }while ( !(ar_SetNi==ar_SetNi_1) );
      }while ( !(ar_SetNi->Comparation(ar_SetNi_1)) );

      if (ar_SetN.Is(vc_StartNoTerm))
       {if (ar_SetN==ar_SetNi)
	   {vn_RetCase = 1;}
	else
	   {ar_SetN=ar_SetNi;
	    vn_RetCase = 2; } }
      else
       {vn_RetCase = 0;}

      // ��⠢��� ⮫쪮 � �ࠢ��� ����� ᮤ�ঠ� ᨬ���� �� N U E
      for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
       {for (j=0;j<TablRuls[i]->RealR;j++)//��ॡ�� ��� �ࠢ�� � ������ ��.
	 { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	   // �᫨ �ࠢ��� 㤮���⢮��� �᫮���, �� �� ᨬ���� � ���
	   // �ਭ������� N U E � ��� ��⠢���
	   vl_Is=1;
	   while((vp_point) && (vl_Is))
	    {vc_S = this->NextSymbol(vp_point,vc_Symbol);//�뤥���� ᫥�.
							 // ᬢ�� � �ࠢ���
	     if (vc_S=='N')// �᫨ �� ���ନ���
	       {vl_Is=ar_SetN.Is(vc_Symbol);}
	     else  // �᫨ �� �ନ���
	       {if (vc_S =='T')
		  vl_Is=ar_SetE.Is(vc_Symbol);} }
	   if (!vl_Is)// �᫨ �� ��. �᫮��� (��. ��� �)
	    {this->DeleteRule(TablRuls[i]->NoTerm,j);}// 㤠���� �� �ࠢ���
	 }
       }
      for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
       { if (TablRuls[i]->RealR==0)// �᫨ � ���ନ���� ��� �ࠢ�� � ��� ���.
	   {delete TablRuls[i];
	    for (j=i;j<RealRuls-1;j++)
	     {TablRuls[j]=TablRuls[j+1];}
	    RealRuls--;
	    TablRuls[RealRuls] = NULL;
	   }
       }

      delete ar_SetNi;
      delete ar_SetNi_1;

      return vn_RetCase;
     }


  int StructRuls::Algoritm_DelNonSymbol()// �������� �����⨦���� ᨬ�����
      // ������ �᭮��� �� �८�ࠧ������ �ࠬ��⨪� ���ᠭ��� � �����
      // �.��, ��.��쬠� ����� ᨭ⠪��᪨�� �������, ��ॢ��� �
      // �������樨 ��� 1 ���⠪��᪨� ������  ���. 171
     {
      int j=0,vl_Is=0,vn_RetCase=0,vn_RealR=0;
      char *vp_point=NULL,vc_S,vc_Symbol[256],vc_SymbolX[256];
      char *vp_NoTerm=NULL,*vp_Symbol=NULL;
      SetStr *ar_SetVi=NULL,*ar_SetVi_1=NULL;
      // TablRuls
      ar_SetVi = new SetStr();
      ar_SetVi_1 = new SetStr();

      ar_SetVi->AddElem(vc_StartNoTerm);
      do{
//	 ar_SetVi_1 = ar_SetVi;
	 ar_SetVi_1->Appropriation(ar_SetVi);
	 ar_SetVi_1->InitStack();
	 vp_NoTerm = ar_SetVi_1->RetElem();// ����砥� 1-� ���ନ���
	 vn_RealR = this->ReturnRealR(vp_NoTerm);// �᫮ �ࠢ�� ��� ����.
	 while (vp_NoTerm) // ��ॡ�� ��� ���ନ����� �ਭ�������� ar_SetVi_1
	  {for (j=0;j<vn_RealR;j++)//��ॡ�� ��� �ࠢ�� � ������� ��.
	    { vp_point = this->ReturnRule(vp_NoTerm,j);
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// �ய�����
	      // ���� ���ନ��� ⠪ ��� �ࠢ��� ��稭����� �
	      // ���樠�������饣� ���ନ���� � ��� �� �ய�᪠��

	      // �᫨ �ࠢ��� 㤮���⢮��� �᫮���
	      // {X | (A->aXb �ਭ������� P) � ��ப�- a � b �ਭ��. V(i-1)*}
	      // � A �ਭ��. V(i-1) � ��쥤����� ᨬ��� (X) � ar_SetVi
	      vl_Is=1;
	      while((vp_point) && (vl_Is))
	       {vc_S = this->NextSymbol(vp_point,vc_Symbol);//�뤥���� ᫥�.
		// ᨬ��� � �ࠢ���
		if (vc_S!='E') {vl_Is=ar_SetVi_1->Is(vc_Symbol);}
		// �஢���� �ਭ������� �� ��� ᨬ��� ��������
		}
	      if (!vl_Is)
		// �.�. �� ���� �� ᨬ���� ���⥦��� � � ��� ᨬ��� ���⥦��
		// ����� �� ���� �஢�ઠ �� ��ப� b---??? ���� �� ???
		{ar_SetVi->AddElem(vc_Symbol);}

//	      if (! vl_Is)// �᫨ ��. �᫮��� (��. ��� �), �� �����-�
	      // ᨬ��� ���ਭ������� �������� � �஢�ਬ 楯��� (b) �� ���
//	       {
//		 vl_Is=1;
//		 strcpy(vc_SymbolX,vc_Symbol);// �������� ᨬ��� X
//		 while((vp_point) && (vl_Is)) // �஢��塞 楯��� b ��
		 // �ਭ���������� Vi-1
//		  {vc_S = this->NextSymbol(vp_point,vc_Symbol);//�뤥���� ᫥�.
		   // ᨬ��� � �ࠢ���
//		   if (vc_S!='E') {vl_Is=ar_SetVi_1.Is(vc_Symbol);}
		   // �஢���� �ਭ������� �� ��� ᨬ��� ��������
//		   }
//		 if (vl_Is)// ������塞 ᨬ���
//		  {ar_SetVi.AddElem(vc_SymbolX);}
//	       }

	    }
	   vp_NoTerm = ar_SetVi_1->RetElem();// ����砥� ᫥�. ᨬ���
	   // �.�. ᫥�. ᨬ����� ����� ���� �ନ��� � ���� �।�ᬮ����
	   // ��� �ய��. �� ���⨣����� ⥬ �� �����頥��� �᫮ �ࠢ��
	   // ��� ���� = -1
	   vn_RealR = this->ReturnRealR(vp_NoTerm);// �᫮ �ࠢ�� ��� ����.
	  }
//      }while ( !(ar_SetVi== ar_SetVi_1) );
      }while ( !(ar_SetVi->Comparation(ar_SetVi_1)) );

      // �ନ�㥬 N'= Vi ����祭�� � N
      ar_SetVi_1->InitSet();
      ar_SetN.InitStack();
      vp_Symbol = ar_SetN.RetElem();
      while(vp_Symbol)
       {if (ar_SetVi->Is(vp_Symbol))
	 {ar_SetVi_1->AddElem(vp_Symbol);}
	vp_Symbol = ar_SetN.RetElem();
       }
      ar_SetN1=ar_SetVi_1;

      // �ନ�㥬 E'= Vi ����祭�� � E
      ar_SetVi_1->InitSet();
      ar_SetE.InitStack();
      vp_Symbol = ar_SetE.RetElem();
      while(vp_Symbol)
       {if (ar_SetVi->Is(vp_Symbol))
	 {ar_SetVi_1->AddElem(vp_Symbol);}
	vp_Symbol = ar_SetE.RetElem();
       }
      ar_SetE1=ar_SetVi_1;

      if ((ar_SetN==ar_SetN1) && (ar_SetE==ar_SetE1))
	{vn_RetCase = 1;}// �� ������⢠ ࠢ��
      else
	{ if (!(ar_SetN==ar_SetN1))
	   {vn_RetCase = 2;}// ��ࠢ�� ���ନ�. ������⢠
	  else
	   { if (!(ar_SetE==ar_SetE1))
	       {vn_RetCase = 3;}// ��ࠢ�� �ନ�. ������⢠
	     else
	       {vn_RetCase = 4;}
	   }
	}
      ar_SetN=ar_SetN1;
      ar_SetE=ar_SetE1;
	printf("Load Gramm Algoritm End 1: \n");
//	HP();
      delete ar_SetVi;
      delete ar_SetVi_1;
      return vn_RetCase;
     }

/*
  int StructRuls::Algoritm_DelCircleRules()// �������� 楯��� �ࠢ��
      // ������ �᭮��� �� �८�ࠧ������ �ࠬ��⨪� ���ᠭ��� � �����
      // �.��, ��.��쬠� ����� ᨭ⠪��᪨�� �������, ��ॢ��� �
      // �������樨 ��� 1 ���⠪��᪨� ������  ���. 174
     {
      int j=0,vl_Is=0,vn_RetCase=0,vn_RealR=0;
      char *vp_point=NULL,vc_S,vc_Symbol[256],vc_SymbolX[256];
      char *vp_NoTerm,*vp_Symbol;
      // ��� (1)
     }
*/

  int StructRuls::Algoritm_DelReduceRules()// ������ ���� �� ����� ४����
      // ������ �᭮��� �� ������ ����஢�
      // 1) ��室����� �� �ࠢ��� � ������ � �ࠢ�� ��� ���� �⮨� �ନ���
      // 2) ��⥬ ��室����� �� ���ନ���� � ������ �� ��� �ࠢ���� � �ࠢ��
      //    ��� ���� �⮨� �ନ���
      // 3) ��⥬ ��������� 蠣 2 ���� Ni<>Ni-1
      // (��� Ni_-������⢮ ��ନ஢���� �� i-�� �ண��� ��쥤������� �
      // ������⢮� Ni-1; Ni_ e (Ni U Ni-1) )
      // �����頥� 1 �᫨ �� ��ଠ�쭮 � 2 �᫨ ���� ४����
     {
      int i=0,j=0,vl_Is=0,vn_RetCase=0;
      char *vp_point=NULL,vc_S,vc_Symbol[256];
      SetStr *ar_SetNi=NULL,*ar_SetNi_1=NULL;

      ar_SetNi = new SetStr();
      ar_SetNi_1 = new SetStr();
      do{
//	 ar_SetNi_1 = ar_SetNi;
	 ar_SetNi_1->Appropriation(ar_SetNi);
	 for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
	 // ����� ����� �᪮��� ��� ��楤��� �᫨ �� �஢����� ���ନ����
	 // ����� 㦥 �ਭ������� ar_SetNi_1
	  {vl_Is=1; j =0;
	   while ((j<TablRuls[i]->RealR) && (vl_Is))//��ॡ�� ��� �ࠢ�� � ������ ��.
	    { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// �ய�����
	      // ���� ���ନ��� ⠪ ��� �ࠢ��� ��稭����� �
	      // ���樠�������饣� ���ନ���� � ��� �� �ய�᪠��
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// ����� ���� ᨬ���

	      if (vc_S=='N')// �᫨ �� ���ନ���
		  {vl_Is=ar_SetNi_1->Is(vc_Symbol);}
	      else  // �᫨ �� �ନ���
		  {if (vc_S =='T')
		     vl_Is=ar_SetE.Is(vc_Symbol);}
	      j++; }
	   // ��ॡ�� ��� �ࠢ�� � ���ନ���� �����祭
	   // �᫨ �� �ࠢ��� 㤮���⢮��� �᫮���
	   // {A | (A->a �ਭ������� P) � ���� ���ନ���a ��ப�-a
	   // �ਭ��. (N(i-1)UE)* � ��쥤����� ���ନ��� � ���.
	   // ��稭����� ������ �ࠢ��� (A) � ar_SetNi
	   if (vl_Is)// �᫨ ��. �᫮��� (��. ��� �)
	     {ar_SetNi->AddElem(TablRuls[i]->NoTerm);}// ������塞 ���ନ���
	  }
//      }while ( !(ar_SetNi==ar_SetNi_1) );
      }while ( !(ar_SetNi->Comparation(ar_SetNi_1)) );

      if (ar_SetN==ar_SetNi)
	   {vn_RetCase = 1;}
      else
	   {ar_SetN=ar_SetNi;
	    vn_RetCase = 2; }

      // ��⠢��� ⮫쪮 � �ࠢ��� ����� ᮤ�ঠ� ᨬ���� �� N U E
      for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
       {for (j=0;j<TablRuls[i]->RealR;j++)//��ॡ�� ��� �ࠢ�� � ������ ��.
	 { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	   // �᫨ �ࠢ��� 㤮���⢮��� �᫮���, �� �� ᨬ���� � ���
	   // �ਭ������� N U E � ��� ��⠢���
	   vl_Is=1;
	   while((vp_point) && (vl_Is))
	    {vc_S = this->NextSymbol(vp_point,vc_Symbol);//�뤥���� ᫥�.
							 // ᬢ�� � �ࠢ���
	     if (vc_S=='N')// �᫨ �� ���ନ���
	       {vl_Is=ar_SetN.Is(vc_Symbol);}
	     else  // �᫨ �� �ନ���
	       {if (vc_S =='T')
		  vl_Is=ar_SetE.Is(vc_Symbol);} }
	   if (!vl_Is)// �᫨ �� ��. �᫮��� (��. ��� �)
	    {this->DeleteRule(TablRuls[i]->NoTerm,j);}// 㤠���� �� �ࠢ���
	 }
       }
      for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
       { if (TablRuls[i]->RealR==0)// �᫨ � ���ନ���� ��� �ࠢ�� � ��� ���.
	   {delete TablRuls[i];
	    for (j=i;j<RealRuls-1;j++)
	     {TablRuls[j]=TablRuls[j+1];}
	    RealRuls--;
	    TablRuls[RealRuls] = NULL;
	   }
       }

      delete ar_SetNi;
      delete ar_SetNi_1;
      return vn_RetCase;
     }

  void StructRuls::ShowRuls()// ��ᯥ���� �� �ࠢ���
     { int i,j;
       char *vp_point=NULL;

      for (i=0;i<RealRuls;i++) // ��ॡ�� ��� ���ନ�����
       {for (j=0;j<TablRuls[i]->RealR;j++)//��ॡ�� ��� �ࠢ�� � ������ ��.
	 { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	   printf("%i-rule  % s \n",j,vp_point);
	 }
       }
     }

  void StructRuls::DeleteRuls()// ������� ��� ⠡����
     {
      int pi1,pj1;

      for (pi1=0;pi1<RealRuls;pi1++)
       { delete TablRuls[pi1]; }
      this->InitRuls();
     }


  int StructRuls::LoadRuls(char *FileN)// ����� ⠡���� � ��᪠
     {
      FILE *pOf=NULL;
      int vn_Ferst=1,i2=0,pbg=0;
      Ruls *Rl=NULL;
      char *vp_point=NULL,vc_Symbol[256];

      // �⮣� ����� �������� ����
      if ((pOf = fopen(FileN, "r"))== NULL)
       {fprintf(stderr, "Cannot open input file.\n");
	fclose(pOf);
	return 1;}
      //---------------------------

      this->DeleteRuls();
      pbg = fReadLn(pOf);

      while (pbg)
       {Rl = new(Ruls);                    // ���뢠�� ���� ���ନ���
	strcpy(Rl->NoTerm,(char *)MBuffer);
	if (vn_Ferst)
	 {strcpy(vc_StartNoTerm,Rl->NoTerm);//��砫�� ���ନ���
	  vn_Ferst = 0;}
	i2 =0;
	do{   // ���뢠�� �ࠢ��� ��� ������� ���ନ����
	  pbg=fReadLn(pOf); vp_point = (char *)MBuffer;
	  this->NextSymbol(vp_point,vc_Symbol);
	  if (pbg)
	   {if (strcmp(vc_Symbol,Rl->NoTerm)==0)
	    {strcpy(Rl->Rule[i2],(char *)MBuffer);
	     i2++; } }
	  else
	   {if (pbg!=0)
	    goto LoadRuleEnd;}
	}while (pbg && (strcmp(vc_Symbol,Rl->NoTerm)==0) );
	Rl->RealR = i2;    // ��᫮ �ࠢ�� ��� ����
	this->AddRuls(Rl); // ������塞 ����� ����. � ��� �ࠢ����� �
			   // ����� ⠡���� ���ନ�����
       }
  LoadRuleEnd:
      if (pbg == -1)
       {this->DeleteRuls();} // �᫨ �訡�� � 㤠���� ��� ⠡����
      else
       {
	printf("Init Noterm : \n"); HP();
	pbg = 1;
	this->InitNoTermAndTerm();// ���� ���樠����஢��� ��䠢�� � ����.
//	printf("End Init Noterm : \n");	HP();
	pbg=this->Algoritm_IsGammaticEmpty();// �஢���� ���� �� �ࠬ��⨪�
	// � �᫨ �� ����� � ����� �� ��� �ᯮ�짮������ ��� ���������
	// �᫨ pdg = 2 � �ࠬ�⨪� ������ ����������
	pbg=this->Algoritm_DelNonSymbol();
	pbg=this->Algoritm_DelReduceRules();// ������ ���� �� ����� ४����
	// �����頥� 1 �᫨ �� ��ଠ�쭮 � 2 �᫨ ���� ४����
	printf("Load Gramm Algoritm End after delete: \n"); HP();
       }
      fclose(pOf);
      delete [] pOf;
      return pbg;
     }

  int StructRuls::SaveRuls(char *FileN)// ������� ⠡���� �� ���
     {
      FILE *pOf=NULL;
      int pN,i2=0;

      // �⮣� ����� �������� ����
      if ((pOf = fopen(FileN, "w"))== NULL)
       {fprintf(stderr, "Cannot open input file.\n");
	return 1;}
      //---------------------------

      pN=0;
      while ( pN < RealRuls)
       {fprintf(pOf,"%s",TablRuls[pN]->NoTerm);
	fprintf(pOf,"%c",'\n');
	i2 = 0;
	while ( i2<TablRuls[pN]->RealR)
	 {fprintf(pOf,"%s",TablRuls[pN]->Rule[i2]);
	  fprintf(pOf,"%c",'\n');
	  i2++;}
	pN++;
       }

      fclose(pOf);
      delete [] pOf;
      return 0;
     }

//End StructRuls ----------------------------------------------------------


// End Class SetOfSet
//---------------------------------------------------------------------------
extern StructRuls 		*TRuls;