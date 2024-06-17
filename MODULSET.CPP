
const NRule=30;  // максимальное чило правил для одного нетерминала
const CNRule=50; // общее число таких нетерминалов
const NLenStr=80; // длина правила и названия нетерминала

// следующие 2 константы используются классом SetStr который делает из
// строк множество
const NSet=30; // <- макс. число строк
const NChar=40; // <- макс. длина одной строки

extern void HP();

//--------------------------------------------------------------------------
// Класс объектов для работы со строками (с множеством)
// (вспомогательные классы)
//--------------------------------------------------------------------------


// Class SetStr ------------------------------------------------------------
//typedef  char TElem[NChar];	// Строка
//typedef  TElem TSet[NSet];	// Таблица строк

class SetStr{
protected:
   char		MSet[NSet][NChar];	// Таблица строк (множество)
   int		RElem;  // Число элементов в таблице
   int		itmpRElem;  // промежуточный номер элемента в таблице

public:
   SetStr(){RElem = 0;}; // Конструктор
   ~SetStr();            // Деструктор
   int Is(char *el);     // Процедура проверяющаяя присутствие в таблице MSet
			 // строки el
   int AddElem(char *el);// Добавить в таблицу элемент el
   void InitStack(){itmpRElem=-1;};        // Инициирует itmpRElem;
   char *RetElem()       // Возвращает или следующий элемент
			 // или (если они закончились) NULL
     { itmpRElem+=1;
       if (itmpRElem<RElem)
	 {return MSet[itmpRElem];}
       else
	{return NULL;}
     };
   void InitSet(){RElem = 0;};	  // инициализирует RElem

   int  operator ==(SetStr Set1); // сравнивает 2 множества
   int  operator ==(SetStr *Set1); // сравнивает 2 множества
   int  Comparation(SetStr *Set1);//сравнить множество this с множеством Set1

   void operator  =(SetStr Set1); // присвоение множеств
   void operator  =(SetStr *Set1); // присвоение множеств
   void Appropriation(SetStr *Set1);//присвоить множеству this множество Set1

};
// End Class SetStr --------------------------------------------------------


// Class SetOfSet ------------------------------------------------------------
struct TSSet {        // Таблица таблиц
   char         NameClass[NChar];
   SetStr 	ListOfClass;
 };

class SetOfSet{
protected:
   TSSet	*pList[NSet];	// Список таблиц (множество)
   int		RElem;  	// Число элементов в таблице
   int		itmpRElem;  	// промежуточный номер элемента в таблице

public:
   SetOfSet(){pList[0]=NULL;RElem = 0;itmpRElem=0;} // Конструктор
   ~SetOfSet();         			    // Деструктор
   int IsElem(char *ClassOfElem,char *Elem);
	// Процедура проверяющаяя присутствие в классе ClassOfElem
	// строки el
   int IsClass(char *ClassOfElem);
	// Процедура проверяющаяя присутствие класса ClassOfElem
   int AddElem(char *ClassOfElem,char *Elem);
	// Добавить в класс ClassOfElem элемент el. Если такого класса
	// нет то процедура его создаст.
   void InitStack(){itmpRElem=-1;}// Инициирует itmpRElem
   char *RetClass()	 // Возвращает или следующий класс
			 // или (если они закончились) NULL
     { itmpRElem+=1;
       if (itmpRElem<RElem)
	 {pList[itmpRElem]->ListOfClass.InitStack();
	  return pList[itmpRElem]->NameClass;}
       else
	{return NULL;}
     };

   char *RetElemOfClass()// Возвращает или следующий элемент класса
			 // определенного RetClass или (если они закончились)
			 // NULL
     { if (itmpRElem<RElem)
	 {return pList[itmpRElem]->ListOfClass.RetElem();}
       else
	{return NULL;}
     };
};

// End Class SetOfSet --------------------------------------------------------

//--------------------------------------------------------------------------
// Класс объектов для хранения правил грамматики
//--------------------------------------------------------------------------
typedef  char vc_StrRuls[NLenStr];

struct Ruls{ // структура для хранения правил грамматики
 char NoTerm[NLenStr]; // название нетерминала к которому относятся правила
 vc_StrRuls Rule[NRule]; // правила грамматики
		    // их максимальное число определяется NRule
 int   RealR; // число правил для данного нетерминала
};

typedef  Ruls *ArRuls[CNRule];


class StructRuls {
protected:
//---------------------
  ArRuls  TablRuls; // Таблица правил для нетерминалов (в виде записей
		    // типа Ruls)
		    // максимальное число нетерминалов CNRule
  int	  RealRuls; // число нетерминалов для данной грамматики
  int     vn_NomerNoTerm; // для перебора нетерминалов
  SetStr  ar_SetN;  // множество нетерминалов(в грамматиках обозначается N)
  SetStr  ar_SetE;  // множество терминалов или алфавит
		    // (в грамматиках обозначается E)
  SetStr  ar_SetN1; // промежуточное множество нетерминалов
  SetStr  ar_SetE1; // промежуточное множество терминалов
  char    vc_StartNoTerm[256]; // Начальный нетерминал грамматики
//---------------------

public:

  StructRuls(){InitRuls();
	    vn_NomerNoTerm=0;};  	// Конструктор
  int NumberNoTerm(char *Name); 	// по имени нетерминала Name дает
					// его номер в таблице нетерминалов
					// TablRuls
  void InitRuls(); 		        // Инициализирует таблицу NULL-ми
  int AddRuls(Ruls * Rl); 	        // Добавляет новый нетерминал в табл.
					// вх запись типа Ruls
  int AddRul(char * NoTerm,char * Rl);  // Добавляет новое правило в табл.
					// для нетерминала NoTerm
  int DeleteRule(char *NoTerm,int vn_Number);
	// Удалить правило vn_Number у нетерминала NoTerm
  char *ReturnRule(char *NoTerm,int Nr);// По названию нетерминала NoTerm и
					// номеру правила возвращает правило
  int ReturnRealR(char *NoTerm);        // Возвращает по номеру нетерминала
					// число правил для него
  char NextSymbol(char *&vc_StrInput, char *vc_Symbol);
  void InitNoTermAndTerm();			// Инициализирует множество
	// нетерминальных символов
	// Берутся все правила и все нетерминалы найденные в них
	// обьединяются в множество ar_SetN, а все терминалы в ar_SetT

  int Algoritm_IsGammaticEmpty(); 	// Проверяет пуста ли грамматика
      // Алгоритм основан на преобразовании грамматики описанной в книге
      // А.Ахо, Дж.Ульман Теория синтаксическиго анализа, перевода и
      // компиляции Том 1 Синтаксический анализ  Стр. 169

  int Algoritm_DelNonSymbol();// Удаление недостижимых символов
      // Алгоритм основан на преобразовании грамматики описанной в книге
      // А.Ахо, Дж.Ульман Теория синтаксическиго анализа, перевода и
      // компиляции Том 1 Синтаксический анализ  Стр. 171

  int Algoritm_DelReduceRules();// Смотрит есть ли левая рекурсия
      // Алгоритм основан на лекциях Макарова
      // 1) Находяться все правила у которых в правой части первым стоит терминал
      // 2) Затем находяться все нетерминалы у которых во всех правилах в правой
      //    части первым стоит терминал
      // 3) Затем повторяется шаг 2 пока Ni_<>Ni-1
      // (где Ni_-множество сформированные на i-ом прогоне обьедененное с
      // множеством Ni-1; Ni_ e (Ni U Ni-1) )
      // Возвращает 1 если все нормально и 2 если есть рекурсия

  void ShowRuls();			// Распечатать все правила
  void DeleteRuls();                    // Удалить всю таблицу
  int LoadRuls(char *FileN);            // Считать таблицу с диска
  int SaveRuls(char *FileN);            // Записать таблицу на диск
  ~StructRuls(){DeleteRuls();};  	// Деструктор

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

   int SetStr::Is(char *el)// Процедура проверяющаяя присутствие в таблице MSet
	// строки el
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

   int SetStr::AddElem(char *el)	// Добавить в таблицу элемент el
      {if (RElem<CNRule)
	 {if (! this->Is(el))
	   { strcpy(MSet[RElem],el);
	     RElem++;}  }
       else
	 {return 0;}
       return 1;
      }


   int SetStr::operator ==(SetStr Set1) // сравнивает 2 множества
     {
      char *pc_SymbolA=NULL;  // и если они совпадают то выдает 1 иначе 0
      int   vl_Equal;

      this->InitStack();
      vl_Equal=1;
      pc_SymbolA = this->RetElem();
      while((pc_SymbolA) && (vl_Equal) )
	{ vl_Equal = Set1.Is(pc_SymbolA) ;
	  pc_SymbolA = this->RetElem();	}

      return vl_Equal;
     };

   int SetStr::operator ==(SetStr *Set1) // сравнивает 2 множества
     {
      char *pc_SymbolA=NULL;  // и если они совпадают то выдает 1 иначе 0
      int   vl_Equal;

      this->InitStack();
      vl_Equal=1;
      pc_SymbolA = this->RetElem();
      while((pc_SymbolA) && (vl_Equal) )
	{ vl_Equal = Set1->Is(pc_SymbolA) ;
	  pc_SymbolA = this->RetElem();	}

      return vl_Equal;
     };

   void SetStr::operator =(SetStr Set1) // присвоение множеств
     {char *pc_SymbolA=NULL;

      Set1.InitStack();
      pc_SymbolA = Set1.RetElem();
      this->InitSet();
      while( pc_SymbolA )
	{this->AddElem(pc_SymbolA);
	 pc_SymbolA = Set1.RetElem();}

     };

   void SetStr::operator =(SetStr *Set1) // присвоение множеств
     {char *pc_SymbolA=NULL;

      Set1->InitStack();
      pc_SymbolA = Set1->RetElem();
      this->InitSet();
      while( pc_SymbolA )
	{this->AddElem(pc_SymbolA);
	 pc_SymbolA = Set1->RetElem();}

     };

   int SetStr::Comparation(SetStr *Set1)//сравнить множество this с множеством Set1
     {
      char *pc_SymbolA=NULL;  // и если они совпадают то выдает 1 иначе 0
      int   vl_Equal;

      this->InitStack();
      vl_Equal=1;
      pc_SymbolA = this->RetElem();
      while((pc_SymbolA) && (vl_Equal) )
	{ vl_Equal = Set1->Is(pc_SymbolA) ;
	  pc_SymbolA = this->RetElem();	}

      return vl_Equal;
     };

   void SetStr::Appropriation(SetStr *Set1)//присвоить множеству this множество Set1
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
	   // Процедура проверяющаяя присутствие в классе ClassOfElem
	   // строки el
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
	   // Процедура проверяющаяя присутствие класса ClassOfElem
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
	   // Добавить в класс ClassOfElem элемент el. Если такого класса
	   // нет то процедура его создаст.
   { register int i=0,pf=1;
     TSSet	*pntList=NULL;

     if (ClassOfElem != NULL)
      {if ( (! this->IsClass(ClassOfElem))&&(RElem<CNRule) )
	{//если нет такого класса
	 pntList = new (TSSet);
	 strcpy(pntList->NameClass,ClassOfElem);
	 pntList->ListOfClass.AddElem(Elem);
	 pList[RElem]=pntList;
	 RElem++;
	}
       else
	{//если такой клас существует
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

  int StructRuls::NumberNoTerm(char *Name)// по имени нетерминала Name дает
	// его номер в таблице нетерминалов TablRuls
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


  void StructRuls::InitRuls()// Инициализирует таблицу NULL-ми
     {
      register i,j;
      for (i=0;i<CNRule;i++)
       {TablRuls[i] = NULL;}

      RealRuls = 0;
     }

  int StructRuls::AddRuls(Ruls * Rl)// Добавляет новый нетерминал в табл.
	// вх запись типа Ruls
    {
      if (RealRuls<CNRule)
       {TablRuls[RealRuls] = Rl;
	RealRuls +=1;}
      else
       {exit(1);}
      return 0;
    }

  int StructRuls::AddRul(char * NoTerm,char * Rl)// Добавляет новое правило в
	// таблицу для нетерминала NoTerm
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
      // Удалить правило vn_Number у нетерминала NoTerm
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

  char *StructRuls::ReturnRule(char *NoTerm,int Nr)// По названию нетерминала
	// NoTerm и номеру правила возвращает правило или NULL если
	// такого правила нет
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

  int StructRuls::ReturnRealR(char *NoTerm)// Возвращает по названию нетерминала
	// число правил для него
     {
      register i;

      i = NumberNoTerm(NoTerm);
      if ((i == -1)||(i>RealRuls))
       {return -1;}
      else
       {return (TablRuls[i]->RealR);}
     }

  char StructRuls::NextSymbol(char *&vc_StrInput, char *vc_Symbol)
     // выдает след. элемент строки vc_StrInput если он нетерминал
     // то выдается "N" иначе "T"
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
	 vc_StrInput = &vc_StrInput[pi]; // установить указатель на начало
	 pi = 0;                         // след. символа
	 do{                             // считать символ
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

  void StructRuls::InitNoTermAndTerm()	// Инициализирует множество
	// нетерминальных символов
	// Берутся все правила и все нетерминалы найденные в них
	// обьединяются в множество ar_SetN, а все терминалы в ar_SetT
     {char *vp_point=NULL;
      char vc_Symbol[256];
      char vc_S;
      int  i=0,j=0;

      for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
       { for (j=0;j<TablRuls[i]->RealR;j++)//перебор всех правил у одного нт.
	  { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	    while(vp_point)
	     {vc_S = this->NextSymbol(vp_point,vc_Symbol);//выделить след.
							  // смвол в правиле
	      if (vc_S=='N')// если это нетерминал
		{ar_SetN.AddElem(vc_Symbol);}
	      else  // если это терминал
		{if (vc_S =='T')
		   ar_SetE.AddElem(vc_Symbol);} }
	  }
       }
     }


  int StructRuls::Algoritm_IsGammaticEmpty()// Проверяет пуста ли грамматика
      // Алгоритм основан на преобразовании грамматики описанной в книге
      // А.Ахо, Дж.Ульман Теория синтаксическиго анализа, перевода и
      // компиляции Том 1 Синтаксический анализ  Стр. 169
     {
      SetStr *ar_SetNi=NULL,*ar_SetNi_1=NULL;
      int i=0,j=0,vl_Is=0,vn_RetCase=0;
      char *vp_point=NULL,vc_S,vc_Symbol[256];

      ar_SetNi = new SetStr();
      ar_SetNi_1 = new SetStr();
      do{
	 ar_SetNi_1->Appropriation(ar_SetNi);
//	 ar_SetNi_1=ar_SetNi;
	 for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
	 // здесь можно ускорить эту процедуру если не проверять нетерминалы
	 // которые уже принадлежат ar_SetNi_1
	  {for (j=0;j<TablRuls[i]->RealR;j++)//перебор всех правил у одного нт.
	    { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// пропустить
	      // первый нетерминал так как правило начинается с
	      // инициализирующего нетерминала то его мы пропускаем

	      // если правило удовлетворяет условию
	      // {A | (A->a принадлежит P) и строка-a принад. (N(i-1)UE)*} то
	      // обьеденить нетерминал с кот. начинается данное правило (A)
	      // с ar_SetNi
	      vl_Is=1;
	      while((vp_point) && (vl_Is))
	       {vc_S = this->NextSymbol(vp_point,vc_Symbol);//выделить след.
							    // смвол в правиле
		if (vc_S=='N')// если это нетерминал
		  {vl_Is=ar_SetNi_1->Is(vc_Symbol);}
		else  // если это терминал
		  {if (vc_S =='T')
		     vl_Is=ar_SetE.Is(vc_Symbol);} }
	      if (vl_Is)// если вып. условие (См. Выше то)
	       {ar_SetNi->AddElem(TablRuls[i]->NoTerm);}// добавляем нетерминал
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

      // оставить только те правила которые содержат символы из N U E
      for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
       {for (j=0;j<TablRuls[i]->RealR;j++)//перебор всех правил у одного нт.
	 { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	   // если правило удовлетворяет условию, что все символы в нем
	   // принадлежат N U E то его оставить
	   vl_Is=1;
	   while((vp_point) && (vl_Is))
	    {vc_S = this->NextSymbol(vp_point,vc_Symbol);//выделить след.
							 // смвол в правиле
	     if (vc_S=='N')// если это нетерминал
	       {vl_Is=ar_SetN.Is(vc_Symbol);}
	     else  // если это терминал
	       {if (vc_S =='T')
		  vl_Is=ar_SetE.Is(vc_Symbol);} }
	   if (!vl_Is)// если не вып. условие (См. Выше то)
	    {this->DeleteRule(TablRuls[i]->NoTerm,j);}// удалить это правило
	 }
       }
      for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
       { if (TablRuls[i]->RealR==0)// если у нетерминала нет правил то его дел.
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


  int StructRuls::Algoritm_DelNonSymbol()// Удаление недостижимых символов
      // Алгоритм основан на преобразовании грамматики описанной в книге
      // А.Ахо, Дж.Ульман Теория синтаксическиго анализа, перевода и
      // компиляции Том 1 Синтаксический анализ  Стр. 171
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
	 vp_NoTerm = ar_SetVi_1->RetElem();// получаем 1-ый нетерминал
	 vn_RealR = this->ReturnRealR(vp_NoTerm);// число правил для нетерм.
	 while (vp_NoTerm) // перебор всех нетерминалов принадлежащих ar_SetVi_1
	  {for (j=0;j<vn_RealR;j++)//перебор всех правил у данного нт.
	    { vp_point = this->ReturnRule(vp_NoTerm,j);
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// пропустить
	      // первый нетерминал так как правило начинается с
	      // инициализирующего нетерминала то его мы пропускаем

	      // если правило удовлетворяет условию
	      // {X | (A->aXb принадлежит P) и строки- a и b принад. V(i-1)*}
	      // и A принад. V(i-1) то обьеденить символ (X) с ar_SetVi
	      vl_Is=1;
	      while((vp_point) && (vl_Is))
	       {vc_S = this->NextSymbol(vp_point,vc_Symbol);//выделить след.
		// символ в правиле
		if (vc_S!='E') {vl_Is=ar_SetVi_1->Is(vc_Symbol);}
		// проверить принадлежит ли этот символ множеству
		}
	      if (!vl_Is)
		// т.к. до него все символы достежимы то и этот символ достежим
		// здесь не идет проверка на строку b---??? надо ли ???
		{ar_SetVi->AddElem(vc_Symbol);}

//	      if (! vl_Is)// если вып. условие (См. Выше то), что какой-то
	      // символ непринадлежит множеству то проверим цепочку (b) за ним
//	       {
//		 vl_Is=1;
//		 strcpy(vc_SymbolX,vc_Symbol);// запомним символ X
//		 while((vp_point) && (vl_Is)) // проверяем цепочку b на
		 // принадлежность Vi-1
//		  {vc_S = this->NextSymbol(vp_point,vc_Symbol);//выделить след.
		   // символ в правиле
//		   if (vc_S!='E') {vl_Is=ar_SetVi_1.Is(vc_Symbol);}
		   // проверить принадлежит ли этот символ множеству
//		   }
//		 if (vl_Is)// добавляем символ
//		  {ar_SetVi.AddElem(vc_SymbolX);}
//	       }

	    }
	   vp_NoTerm = ar_SetVi_1->RetElem();// получаем след. символ
	   // т.к. след. символом может быть терминал то надо предусмотреть
	   // его пропуск. Это достигается тем что возвращаемое число правил
	   // для него = -1
	   vn_RealR = this->ReturnRealR(vp_NoTerm);// число правил для нетерм.
	  }
//      }while ( !(ar_SetVi== ar_SetVi_1) );
      }while ( !(ar_SetVi->Comparation(ar_SetVi_1)) );

      // формируем N'= Vi пересечение с N
      ar_SetVi_1->InitSet();
      ar_SetN.InitStack();
      vp_Symbol = ar_SetN.RetElem();
      while(vp_Symbol)
       {if (ar_SetVi->Is(vp_Symbol))
	 {ar_SetVi_1->AddElem(vp_Symbol);}
	vp_Symbol = ar_SetN.RetElem();
       }
      ar_SetN1=ar_SetVi_1;

      // формируем E'= Vi пересечение с E
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
	{vn_RetCase = 1;}// все множества равны
      else
	{ if (!(ar_SetN==ar_SetN1))
	   {vn_RetCase = 2;}// неравны нетермин. множества
	  else
	   { if (!(ar_SetE==ar_SetE1))
	       {vn_RetCase = 3;}// неравны термин. множества
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
  int StructRuls::Algoritm_DelCircleRules()// Удаление цепных правил
      // Алгоритм основан на преобразовании грамматики описанной в книге
      // А.Ахо, Дж.Ульман Теория синтаксическиго анализа, перевода и
      // компиляции Том 1 Синтаксический анализ  Стр. 174
     {
      int j=0,vl_Is=0,vn_RetCase=0,vn_RealR=0;
      char *vp_point=NULL,vc_S,vc_Symbol[256],vc_SymbolX[256];
      char *vp_NoTerm,*vp_Symbol;
      // ШАГ (1)
     }
*/

  int StructRuls::Algoritm_DelReduceRules()// Смотрит есть ли левая рекурсия
      // Алгоритм основан на лекциях Макарова
      // 1) Находяться все правила у которых в правой части первым стоит терминал
      // 2) Затем находяться все нетерминалы у которых во всех правилах в правой
      //    части первым стоит терминал
      // 3) Затем повторяется шаг 2 пока Ni<>Ni-1
      // (где Ni_-множество сформированные на i-ом прогоне обьедененное с
      // множеством Ni-1; Ni_ e (Ni U Ni-1) )
      // Возвращает 1 если все нормально и 2 если есть рекурсия
     {
      int i=0,j=0,vl_Is=0,vn_RetCase=0;
      char *vp_point=NULL,vc_S,vc_Symbol[256];
      SetStr *ar_SetNi=NULL,*ar_SetNi_1=NULL;

      ar_SetNi = new SetStr();
      ar_SetNi_1 = new SetStr();
      do{
//	 ar_SetNi_1 = ar_SetNi;
	 ar_SetNi_1->Appropriation(ar_SetNi);
	 for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
	 // здесь можно ускорить эту процедуру если не проверять нетерминалы
	 // которые уже принадлежат ar_SetNi_1
	  {vl_Is=1; j =0;
	   while ((j<TablRuls[i]->RealR) && (vl_Is))//перебор всех правил у одного нт.
	    { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// пропустить
	      // первый нетерминал так как правило начинается с
	      // инициализирующего нетерминала то его мы пропускаем
	      vc_S = this->NextSymbol(vp_point,vc_Symbol);// взять первый символ

	      if (vc_S=='N')// если это нетерминал
		  {vl_Is=ar_SetNi_1->Is(vc_Symbol);}
	      else  // если это терминал
		  {if (vc_S =='T')
		     vl_Is=ar_SetE.Is(vc_Symbol);}
	      j++; }
	   // перебор всех правил у нетерминала закончен
	   // если все правила удовлетворяет условию
	   // {A | (A->a принадлежит P) и первый нетерминалa строки-a
	   // принад. (N(i-1)UE)* то обьеденить нетерминал с кот.
	   // начинается данное правило (A) с ar_SetNi
	   if (vl_Is)// если вып. условие (См. Выше то)
	     {ar_SetNi->AddElem(TablRuls[i]->NoTerm);}// добавляем нетерминал
	  }
//      }while ( !(ar_SetNi==ar_SetNi_1) );
      }while ( !(ar_SetNi->Comparation(ar_SetNi_1)) );

      if (ar_SetN==ar_SetNi)
	   {vn_RetCase = 1;}
      else
	   {ar_SetN=ar_SetNi;
	    vn_RetCase = 2; }

      // оставить только те правила которые содержат символы из N U E
      for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
       {for (j=0;j<TablRuls[i]->RealR;j++)//перебор всех правил у одного нт.
	 { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	   // если правило удовлетворяет условию, что все символы в нем
	   // принадлежат N U E то его оставить
	   vl_Is=1;
	   while((vp_point) && (vl_Is))
	    {vc_S = this->NextSymbol(vp_point,vc_Symbol);//выделить след.
							 // смвол в правиле
	     if (vc_S=='N')// если это нетерминал
	       {vl_Is=ar_SetN.Is(vc_Symbol);}
	     else  // если это терминал
	       {if (vc_S =='T')
		  vl_Is=ar_SetE.Is(vc_Symbol);} }
	   if (!vl_Is)// если не вып. условие (См. Выше то)
	    {this->DeleteRule(TablRuls[i]->NoTerm,j);}// удалить это правило
	 }
       }
      for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
       { if (TablRuls[i]->RealR==0)// если у нетерминала нет правил то его дел.
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

  void StructRuls::ShowRuls()// Распечатать все правила
     { int i,j;
       char *vp_point=NULL;

      for (i=0;i<RealRuls;i++) // перебор всех нетерминалов
       {for (j=0;j<TablRuls[i]->RealR;j++)//перебор всех правил у одного нт.
	 { vp_point = this->ReturnRule(TablRuls[i]->NoTerm,j);
	   printf("%i-rule  % s \n",j,vp_point);
	 }
       }
     }

  void StructRuls::DeleteRuls()// Удалить всю таблицу
     {
      int pi1,pj1;

      for (pi1=0;pi1<RealRuls;pi1++)
       { delete TablRuls[pi1]; }
      this->InitRuls();
     }


  int StructRuls::LoadRuls(char *FileN)// Считать таблицу с диска
     {
      FILE *pOf=NULL;
      int vn_Ferst=1,i2=0,pbg=0;
      Ruls *Rl=NULL;
      char *vp_point=NULL,vc_Symbol[256];

      // этого здесь недолжно быть
      if ((pOf = fopen(FileN, "r"))== NULL)
       {fprintf(stderr, "Cannot open input file.\n");
	fclose(pOf);
	return 1;}
      //---------------------------

      this->DeleteRuls();
      pbg = fReadLn(pOf);

      while (pbg)
       {Rl = new(Ruls);                    // Открываем новый нетерминал
	strcpy(Rl->NoTerm,(char *)MBuffer);
	if (vn_Ferst)
	 {strcpy(vc_StartNoTerm,Rl->NoTerm);//начальный нетерминал
	  vn_Ferst = 0;}
	i2 =0;
	do{   // считываем правила для данного нетерминала
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
	Rl->RealR = i2;    // Число правил для него
	this->AddRuls(Rl); // добавляем данный нетерм. с его правилами в
			   // общую таблицу нетерминалов
       }
  LoadRuleEnd:
      if (pbg == -1)
       {this->DeleteRuls();} // если ошибка то удалить всю таблицу
      else
       {
	printf("Init Noterm : \n"); HP();
	pbg = 1;
	this->InitNoTermAndTerm();// иначе инициализировать алфавит и нетерм.
//	printf("End Init Noterm : \n");	HP();
	pbg=this->Algoritm_IsGammaticEmpty();// Проверяет пуста ли грамматика
	// и если не пустая то может ли она использоваться без изменений
	// если pdg = 2 то граммтика должна измениться
	pbg=this->Algoritm_DelNonSymbol();
	pbg=this->Algoritm_DelReduceRules();// Смотрит есть ли левая рекурсия
	// Возвращает 1 если все нормально и 2 если есть рекурсия
	printf("Load Gramm Algoritm End after delete: \n"); HP();
       }
      fclose(pOf);
      delete [] pOf;
      return pbg;
     }

  int StructRuls::SaveRuls(char *FileN)// Записать таблицу на диск
     {
      FILE *pOf=NULL;
      int pN,i2=0;

      // этого здесь недолжно быть
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
