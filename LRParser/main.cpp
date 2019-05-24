#define _CRT_SECURE_NO_WARNINGS

//page 1~2 xxxxx
//page 3

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

#define MaxSymbols 200
#define MaxRules 100
#define MaxNumberOfStates 200

#define EOF_TOK 48
#define URT 48  
// URT hw1 에서 추가

typedef struct tkt	//하나의 토큰을 나타내는 구조체
{
	int kind;		//Kind: 토큰의 종류를 나타냄, 즉 토큰 번호를 말함.
	char sub_kind[3];	//relop 토큰인 경우 다시 구분하는데 이용됨.
	int sub_data;		//ID 토큰의 심볼테이블 엔트리 번호, 양의 정수 값을 저장함.
	double rnum;		//실수인 경우
	char str[20];		//토큰을 구성하는 스트링
}tokentype;


typedef char oneword[50];

char keyword[17][50] = { "if", "else", "while", "do", "for", "include", "define", "typedef", "struct", "int", "char", "float", "double", "void", "return", "case", "then" };
int total_keywords = 17;
int idx_First_keyword = 31;

typedef struct sybtbl { oneword idstr; int atrribute; } sym_ent;	//symbol table의 한 엔트리의 구조
sym_ent symtbl[500];
int total_ids = 0;		//심볼테이블에서 다음에 넣을 엔트리 번호
//////////////////////

//page 4
typedef struct typeitemnode* ty_ptr_item_node;
typedef struct typeitemnode
{
	int RuleNum;
	int DotNum;
	ty_ptr_item_node link;
} type_item;

typedef struct statenode* state_node_ptr;
typedef struct statenode
{
	int id;
	int item_cnt;
	ty_ptr_item_node item_start;
	state_node_ptr next;
} state_node;

typedef struct ssym
{
	int kind;
	int no;
	char str[10];
} sym;
//////////////애 순서 바꿈 밑에 sym 사용하기 때문에
typedef struct itemnode* Arc_node_ptr;
typedef struct itemnode
{
	int from_state;	//rule number
	int to_state;	// point 
	sym gram_sym;	//symbol
	Arc_node_ptr link;
} Arc_node;

typedef struct gotoset* goto_set_ptr;
typedef struct gotoset
{
	Arc_node_ptr Arc_list;
	state_node_ptr State_Node_List;
} goto_set;

typedef struct cell_action_tbl
{
	char Kind;	// s, r, a, e, 중 한 글자
	int num;	// s 이면 state number, r이면 rule number
} ty_Cell_Action_Table;



typedef struct orule
{
	sym leftside;
	sym rightside[10];
	int rleng;
} onerule;

/////////////////////


//page 5

typedef struct nodetype* Ty_Node_Ptr;
typedef struct nodetype
{
	int state;
	sym nodesym;
	int child_cnt;
	Ty_Node_Ptr children[10];
	int rule_no_used;
} nodeT;

//////////////////////


//page 6 = 7

int MaxTerminal;
int MaxNonTerminal;
sym Nonterminals_list[MaxSymbols];
sym Terminals_list[MaxSymbols];

int totalNumberOfRules;
onerule rules[MaxRules];

int FirstTable[MaxSymbols][MaxSymbols];
int FollowTable[MaxSymbols][MaxSymbols];
goto_set_ptr States_And_Arcs = NULL;

int Number_Of_States = 0;
int NumberOfArcs = 0;
ty_Cell_Action_Table Action_Table[MaxNumberOfStates][MaxSymbols];
int Goto_Table[MaxNumberOfStates][MaxSymbols];
Ty_Node_Ptr Stack[1000];
int Top = -1;
Ty_Node_Ptr Root = NULL;
int bar[100];

FILE* fps;

///////////////

int iswhitespace(char c);
int lookup_keyword_tbl(char* str);
int lookup_symtbl(char* str);


/////////////

// page 31.
state_node_ptr Add_A_State_Node(state_node_ptr State_Node_List_Header, ty_ptr_item_node To_list);
void Add_An_Arc(Arc_node_ptr* Arc_List_Header, int from_num, int to_num, sym Symbol);
int CheckExistItem(ty_ptr_item_node cs_list, ty_ptr_item_node s_val);
void Clear_Action_Table(void);
void Clear_Goto_Table(void);
ty_ptr_item_node closure(ty_ptr_item_node IS);
int Compute_first_of_one_nonterminal(sym X);
int Compute_first_of_any_string(sym alpha[], int first_result[]);
int Compute_follow_of_one_nonterminal(int idx_NT);
int deleteTyPtrItemNode(ty_ptr_item_node item_list);
int findToStateNodeId(Arc_node_ptr arc_list, int from_id, sym symbal);
void fitemListPrint(ty_ptr_item_node IS, FILE* fpw);

ty_ptr_item_node getLastItem(ty_ptr_item_node cs_list);

//get_next_token

ty_ptr_item_node GoTo(ty_ptr_item_node IS, sym sym_val);
void printGotoGraph(goto_set_ptr gsp);
//void itemListPrint(ty_ptr_item_node IS); // 사용 안해서 빼둠
tokentype lexan(FILE* fps);
int lookUp_nonterminal(char* str);
int lookUp_terminal(char* str);
void Make_Action_Table();
void Make_Goto_Table();
Arc_node_ptr makeArcNode(void);
void makeGotoGraph(ty_ptr_item_node IS_O);
state_node_ptr makeStateNode(void);
Ty_Node_Ptr Parsing(FILE* fps);
void print_Action_Table(void);
void print_Goto_Table(void);
void print_parse_tree(FILE* fout, Ty_Node_Ptr curr, int standard, int first, int child);
void push_state(Ty_Node_Ptr Stack[], int state);
void push_symbol(Ty_Node_Ptr stack[], Ty_Node_Ptr NodeToPush);
Ty_Node_Ptr pop();
void read_grammar(const char* filename);

//추가함
int itemListCounter(ty_ptr_item_node IS);
int is_same_two_itemlists(ty_ptr_item_node list1, ty_ptr_item_node list2);


//sym get_next_token();
sym get_next_token(FILE* fps);
//이거로 바꿈



// page 30
int main()
{
	int i, j;
	sym a_nonterminal = { 1, 0 };
	read_grammar("Grammar_data.txt");
	strcpy(Terminals_list[MaxTerminal].str, "Epsilon");

	for (i = 0; i < MaxNonTerminal; i++)
	{
		for (j = 0; j < MaxTerminal + 1; j++)
		{
			FirstTable[i][j] = 0;
			FollowTable[i][j] = 0;
		}
		FirstTable[i][MaxTerminal + 1] = 0;
	}

	for (i = 0; i < MaxNonTerminal; i++)
		if (FirstTable[i][MaxTerminal + 1] == 0)
		{
			a_nonterminal.no = i;
			Compute_first_of_one_nonterminal(a_nonterminal);
		}


	FollowTable[0][MaxTerminal - 1] = 1;
	for (i = 0; i < MaxNonTerminal; i++)
	{
		if (FollowTable[i][MaxTerminal] == 0)
			Compute_follow_of_one_nonterminal(i);
	}

	for (i = 0; i < MaxNonTerminal; i++)
	{
		printf("First(%s): ", Nonterminals_list[i].str);
		for (j = 0; j < MaxTerminal; j++)
		{
			if (FirstTable[i][j] == 1)
				printf("%s  ", Terminals_list[j].str);
		}
		if (FirstTable[i][MaxTerminal] == 1)
			printf(" epsilon");
		printf("\n");
	}

	printf("\n");

	for (i = 0; i < MaxNonTerminal; i++)
	{
		printf("Follow(%s): ", Nonterminals_list[i].str);
		for (j = 0; j < MaxTerminal; j++)
		{
			if (FollowTable[i][j] == 1)
				printf("%s  ", Terminals_list[j].str);
		}
		printf("\n");
	}



	ty_ptr_item_node ItemSet0, tptr;

	tptr = (ty_ptr_item_node)malloc(sizeof(type_item));
	tptr->RuleNum = 0;
	tptr->DotNum = 0;
	tptr->link = NULL;

	ItemSet0 = closure(tptr);

	makeGotoGraph(ItemSet0);
	printGotoGraph(States_And_Arcs);
	//goto table 에러남 지금
	Make_Action_Table();
	print_Action_Table();
	Make_Goto_Table();
	print_Goto_Table();

	fps = fopen("source.txt", "r");

	//parsing 에러남
	Root = Parsing(fps);
	fclose(fps);

	FILE* fpo;
	fpo = fopen("output.txt", "w");
	print_parse_tree(fpo, Root, 0, 0, 0);
	fclose(fpo);

	printf("Program terminates. \n");
}





//page 8
//sym get_next_token()  밑에꺼로 바꿈
sym get_next_token(FILE* fps)
{
	sym token;
	tokentype a_tok;
	a_tok = lexan(fps);   /////////////////////
	token.kind = 0;

	if (a_tok.kind == EOF_TOK)
	{
		token.no = MaxTerminal - 1;
		strcpy(token.str, Terminals_list[MaxTerminal - 1].str);
	}
	else
	{
		token.no = a_tok.kind;
		strcpy(token.str, a_tok.str);
	}
	return token;
}	//get_next_token



/////////////////////////hw1에서 가져온것 . lexan을 위한 함수들///////////////

//민제 : 필요없어보임
//char keywords[16][50] = { "if", "else" ,"while","do","for", "include","define", "typedef","struct","int","char","float","double","void","return" , "case" };

int iswhitespace(char c)
{
	if (c == ' ' || c == '\n' || c == '\t')
		return 1;
	else
		return 0;
}

int lookup_keyword_tbl(char* str)
{
	int i;
	for (i = 0; i < total_keywords; i++)
		if (strcmp(keyword[i], str) == 0) //keywords => keyword
			return i;
	return -1;
}

int lookup_symtbl(char* str) {
	int i;
	for (i = 0; i < total_ids; i++)
		if (strcmp(symtbl[i].idstr, str) == 0)
			return i;
	return -1;
}












//////////////////////////////////////////////////////////////////////

//page 9~10		/hw1에서 가져오기
tokentype lexan(FILE* fps)
{
	int state = 0;
	char c;
	char buf[50];
	int bp = 0; // bp is buffer pointer(다음 넣을 위치).
	int upper_n; // number 토큰에서 소숫점 위 부분 즉 정수 부분을 저장함.
	double fraction; // number 토큰에서 소숫점 아래 부분을 저장함.
	tokentype token;
	int idx, FCNT, sign, Enum;

	while (1)
	{
		switch (state)
		{
		case 0: // 초기 상태. 각 토큰의 첫 글자에 따라서 작업 수행 및 다음 상태 결정함.
			c = fgetc(fps);  // fgetc can be called even if fp is after the end of file.
							  // calling it again still returns EOF(-1) w/o invoking error.
			if (iswhitespace(c)) state = 0;  // this is white space.
			else if (isalpha(c))
			{
				buf[bp] = c;
				bp++; buf[bp] = '\0';
				state = 28;
			}
			else if (isdigit(c))
			{
				buf[bp] = c;
				bp++; buf[bp] = '\0';
				upper_n = c - '0';
				state = 1;
			}
			else if (c == '<') state = 2;
			else if (c == '>') state = 32;
			else if (c == '=') state = 35;
			else if (c == '!') state = 38;
			else if (c == '+') state = 3;
			else if (c == '-') state = 4;
			else if (c == '*') state = 52;
			else if (c == '/') state = 8;
			else if (c == '\\') state = 53;
			else if (c == '%') state = 54;
			else if (c == '.') state = 55;
			else if (c == ',') state = 56;
			else if (c == '(') state = 57;
			else if (c == ')') state = 58;
			else if (c == '{') state = 59;
			else if (c == '}') state = 60;
			else if (c == '[') state = 61;
			else if (c == ']') state = 62;
			else if (c == ':') state = 63;
			else if (c == ';') state = 64;
			else if (c == '"') state = 65;
			else if (c == '\'') state = 66;
			else if (c == '#') state = 67;
			else if (c == '|') state = 68;
			else if (c == '&') state = 5;
			else if (c == EOF) state = 71;

			else {
				token.kind = URT; // 인식할 수 없는 토큰임을 나타냄.
				return token;
			}
			break;

		case 1: // NUM 토큰의 소수점 위 숫자열을 받아 들이는 상태.
			c = fgetc(fps);
			if (isdigit(c))
			{
				buf[bp] = c;
				bp++; buf[bp] = '\0';
				upper_n = 10 * upper_n + c - '0';
				state = 1;
			}
			else if (c == '.')
			{
				buf[bp] = c; bp++;
				buf[bp] = '\0';
				fraction = 0;
				FCNT = 0; state = 9;
			} // 소수점을 나왔으므로 실수를 처리하는 상태로 감.
			else if (c == 'E')
			{
				buf[bp] = c;
				bp++; buf[bp] = '\0';
				fraction = 0;
				state = 16;
			}  // E 가 있는 exponent 처리부로 감.
			else state = 14;
			break;

		case 2: // 글자 < 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '=') state = 30;
			else state = 31;
			break;



			// ******************************************************************************

		case 3: // 글자 + 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '+') state = 47;
			else if (c == '=') state = 45;
			else state = 46;
			break;

			// ******************************************************************************


		case 4: // 글자 - 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '-') state = 48;
			else if (c == '=') state = 49;
			else if (c == '>') state = 51;
			else state = 50;
			break;

		case 5: // 글자 + 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '&') state = 6;
			else state = 7;
			break;

		case 6:
			token.kind = 2; strcpy(token.sub_kind, "");
			strcpy(token.str, "&&");
			return token;
		case 7: // 토큰 & 를 리턴해주는 상태.
			ungetc(c, fps);
			token.kind = 13;
			return token;

		case 8:
			c = fgetc(fps);
			if (c == '/') state = 74;
			else if (c == '*') state = 75;
			else if (c == EOF) state = 73;
			else state = 72;
			break;

		case 9: // 실수의 소수점 이하를 받아 들이는 상태
			c = fgetc(fps);
			if (isdigit(c))
			{
				buf[bp] = c; bp++; buf[bp] = '\0';
				FCNT++; fraction = fraction + (c - '0') / pow(10.0, FCNT); state = 23;
			}
			else if (c == 'E')
			{
				buf[bp] = c;
				bp++;
				buf[bp] = '\0';
				state = 16;
			}
			else if (c == EOF)  state = 26;
			else if (iswhitespace(c)) state = 24;
			else state = 25;
			break;

		case 14: // 양의 정수 토큰을 리턴하는 상태.
			ungetc(c, fps);
			token.kind = 1; strcpy(token.sub_kind, "in"); // 양의 정수를 나타냄.
			token.sub_data = upper_n;
			strcpy(token.str, buf);
			return token;

		case 16:
			c = fgetc(fps);
			if (c == '+')
			{
				buf[bp] = c;
				bp++; buf[bp] = '\0';
				sign = 1;
				state = 17;
			}
			else if (c == '-')
			{
				buf[bp] = c;
				bp++;
				buf[bp] = '\0';
				sign = -1;
				state = 17;
			}
			else if (isdigit(c))
			{
				buf[bp] = c;
				bp++;
				buf[bp] = '\0';
				sign = 1;
				Enum = c - '0';
				state = 18;
			}
			else  state = 25; // error! 		 
			break;

		case 17:
			c = fgetc(fps);
			if (isdigit(c))
			{
				buf[bp] = c;
				bp++; buf[bp] = '\0';
				Enum = c - '0';
				state = 18;
			}
			else state = 25; // error!
			break;

		case 18:
			c = fgetc(fps);
			if (isdigit(c))
			{
				buf[bp] = c;
				bp++;
				buf[bp] = '\0';
				Enum = Enum * 10 + c - '0';
				state = 18;
			}
			else state = 19;
			break;
		case 19:
			ungetc(c, fps);
			token.kind = 1; strcpy(token.sub_kind, "do"); // 실수를 나타냄.
			token.rnum = (upper_n + fraction) * pow(10.0, sign * Enum);
			strcpy(token.str, buf);
			return token;
			//////////////////////////////////////////////////////////////////////
		case 20: // id 나 keyword 
			strcpy(token.str, buf);
			idx = lookup_keyword_tbl(buf); // -1 if not exist.
			if (idx >= 0) { token.kind = idx_First_keyword + idx; return token; }  // Note: first keyword has token index 30.
			// reaches here if it is not a keyword.
			idx = lookup_symtbl(buf); // -1 if not exist.
			if (idx >= 0) { token.kind = 0; token.sub_data = idx; return token; }
			// reaches here if it is not in symbol table.
			strcpy(symtbl[total_ids].idstr, buf); total_ids++;
			token.kind = 0; // ID 토큰임을 나타냄.
			token.sub_data = total_ids - 1; // 이 ID 가 들어 있는 심볼테이블 엔트리 번호.
			return token;
			//////////////////////////////////////////////////////////////////////
		case 23:
			c = fgetc(fps);

			if (isdigit(c))
			{
				buf[bp] = c;
				bp++;
				buf[bp] = '\0';
				FCNT++;
				fraction = fraction + (c - '0') / pow(10.0, FCNT);
				state = 23;
			}

			else if (c == 'E')
			{
				buf[bp] = c;
				bp++;
				buf[bp] = '\0';
				state = 16;
			}
			else state = 24;
			break;
		case 24:
			ungetc(c, fps);
			token.kind = 1;
			strcpy(token.sub_kind, "do"); // 실수를 나타냄.
			token.rnum = upper_n + fraction;
			strcpy(token.str, buf);
			return token;
		case 25:
			token.kind = -1;
			return token;
		case 26:  // do not call ungetc.
			token.kind = 1;
			strcpy(token.sub_kind, "do"); // 실수를 나타냄.
			token.rnum = upper_n + fraction;
			strcpy(token.str, buf);
			return token;
		case 28:
			c = fgetc(fps);
			if (isalpha(c) || isdigit(c) || c == '_')
			{
				buf[bp] = c;
				bp++;
				buf[bp] = '\0';
				state = 28;
			}
			else if (c == EOF) state = 20;
			else	 state = 29;
			break;
		case 29: // id 나 keyword 
			ungetc(c, fps);
			strcpy(token.str, buf);
			idx = lookup_keyword_tbl(buf); // -1 if not exist.
			if (idx >= 0) { token.kind = idx_First_keyword + idx; return token; }  // Note: first keyword has token index 30.
			// reaches here if it is not a keyword.
			idx = lookup_symtbl(buf); // -1 if not exist.
			if (idx >= 0) { token.kind = 0; token.sub_data = idx; return token; }
			// reaches here if it is not in symbol table.
			strcpy(symtbl[total_ids].idstr, buf); total_ids++;
			token.kind = 0; // ID 토큰임을 나타냄.
			token.sub_data = total_ids - 1; // 이 ID 가 들어 있는 심볼테이블 엔트리 번호.
			return token;
		case 30:
			token.kind = 2;
			strcpy(token.sub_kind, "LE");
			strcpy(token.str, "<=");
			return token;
		case 31:
			ungetc(c, fps);
			token.kind = 2;
			strcpy(token.sub_kind, "LT");
			strcpy(token.str, "<");
			return token;
		case 32:
			c = fgetc(fps);
			if (c == '=') state = 33;
			else state = 34;
			break;
		case 33:
			token.kind = 2;
			strcpy(token.sub_kind, "GE");
			strcpy(token.str, ">=");
			return token;
		case 34:
			ungetc(c, fps);
			token.kind = 2;
			strcpy(token.sub_kind, "GT");
			strcpy(token.str, ">");
			return token;
		case 35: // 글자 = 가 나온 후의 처리를 담당하는 상태.
			c = fgetc(fps);
			if (c == '=') state = 36;
			else state = 37;
			break;
		case 36: // 토큰 == 에 대한 처리를 수행하는 상태.
			token.kind = 2;
			strcpy(token.sub_kind, "EQ");
			strcpy(token.str, "==");
			return token;
		case 37: // 토큰 > 에 대한 처리를 수행하는 상태.
			ungetc(c, fps);
			token.kind = 8;
			strcpy(token.str, "=");
			return token;
		case 38:
			c = fgetc(fps);
			if (c == '=') state = 39;
			else state = 40;
			break;
		case 39:
			token.kind = 2;
			strcpy(token.sub_kind, "NE");
			strcpy(token.str, "!=");
			return token;
		case 40:
			ungetc(c, fps);
			token.kind = 10;
			strcpy(token.str, "!"); // NOT		
			return token;
		case 45:
			token.kind = 16;
			strcpy(token.str, "+=");
			return token;
		case 46:
			ungetc(c, fps);
			token.kind = 3;
			strcpy(token.str, "+");
			return token;
		case 47:
			token.kind = 14;
			strcpy(token.str, "++");
			return token;
		case 48:
			token.kind = 15;
			strcpy(token.str, "--");
			return token;
		case 49:
			ungetc(c, fps);
			token.kind = 17;
			strcpy(token.str, "-=");
			return token;
		case 50:
			ungetc(c, fps);
			token.kind = 4;
			strcpy(token.str, "-");
			return token;
		case 51:
			token.kind = 9;
			strcpy(token.str, "->");
			return token;
		case 52:
			token.kind = 5;
			strcpy(token.str, "*");
			return token;
		case 53:
			token.kind = 30;
			strcpy(token.str, "\\");
			return token;
		case 54:
			token.kind = 7;
			strcpy(token.str, "%");
			return token;
		case 55:
			token.kind = 11;
			strcpy(token.str, ".");
			return token;
		case 56:
			token.kind = 12;
			strcpy(token.str, ",");
			return token;
		case 57:
			token.kind = 18;
			strcpy(token.str, "(");
			return token;

		case 58:
			token.kind = 19;
			strcpy(token.str, ")");
			return token;
		case 59:
			token.kind = 20;
			strcpy(token.str, "{");
			return token;
		case 60:
			token.kind = 21;
			strcpy(token.str, "}");
			return token;
		case 61:
			token.kind = 22;
			strcpy(token.str, "[");
			return token;


			// ******************************************************************************

		case 62:
			token.kind = 23;
			strcpy(token.str, "]");
			return token;


			// ******************************************************************************
		case 63:
			token.kind = 24;
			strcpy(token.str, ":");
			return token;
		case 64:
			token.kind = 25;
			strcpy(token.str, ";");
			return token;
		case 65:
			token.kind = 26;
			strcpy(token.str, "\"");
			return token;
		case 66:
			token.kind = 27;		 strcpy(token.str, "'");
			return token;

		case 67:
			token.kind = 28;
			strcpy(token.str, "#");
			return token;
		case 68:
			c = fgetc(fps);
			if (c == '|') 	state = 69;
			else 	 state = 70;
			break;
		case 69:
			token.kind = 2;	strcpy(token.sub_kind, "OR");
			strcpy(token.str, "||");
			return token;
		case 70:
			ungetc(c, fps);
			token.kind = 29;
			strcpy(token.str, "|");
			return token;
		case 71:
			token.kind = EOF_TOK;
			strcpy(token.str, "EOF");
			return token;
		case 72:
			ungetc(c, fps);
			token.kind = 6;
			strcpy(token.str, "/");
			return token;
		case 73:
			token.kind = 6;
			strcpy(token.str, "/");
			return token;
		case 74:
			c = fgetc(fps);
			if (c == '\n') state = 0;
			else if (c == EOF) state = 71;
			else state = 74;
			break;
		case 75:
			c = fgetc(fps);
			if (c == '*') state = 76;
			else if (c == EOF) state = 71;
			else state = 75;
			break;
		case 76:
			c = fgetc(fps);
			if (c == '/') state = 0;
			else if (c == EOF) state = 71;
			else state = 75;
			break;
		default: printf("Unrecognizable token! Stop generating tokens.\n");
			token.kind = URT; strcpy(token.str, "URT");
			return token;
		} // switch
	} //while

}



//page 11

ty_ptr_item_node closure(ty_ptr_item_node IS)
{
	ty_ptr_item_node new_cs = NULL;
	ty_ptr_item_node curr = NULL;
	ty_ptr_item_node cursor = NULL;

	sym SymAfterDot;

	int r_num, d_num;
	int i = 0;

	r_num = d_num = 0;
	curr = IS;

	while (curr)
	{
		r_num = curr->RuleNum;
		d_num = curr->DotNum;

		if (d_num >= rules[r_num].rleng)
		{
			curr = curr->link;
			continue;
		}
		else
			SymAfterDot = rules[r_num].rightside[d_num];

		if (!SymAfterDot.kind)
		{
			curr = curr->link;
			continue;
		}

		for (i = 0; i < totalNumberOfRules; i++)
		{
			if (rules[i].leftside.no != SymAfterDot.no)
				continue;

			new_cs = (ty_ptr_item_node)malloc(sizeof(type_item));

			new_cs->RuleNum = i;
			//////////////////// p11 빈칸 O //////////////////////////////////////
			new_cs->DotNum = 0;
			new_cs->link = NULL;

			if (CheckExistItem(IS, new_cs))
			{
				free(new_cs);
				continue;
			}

			cursor = getLastItem(IS);
			cursor->link = new_cs;
		}

		curr = curr->link;
	}
	return IS;
}

int CheckExistItem(ty_ptr_item_node cs_list, ty_ptr_item_node s_val)
{
	ty_ptr_item_node cursor = cs_list;

	while (cursor)
	{
		if (cursor->RuleNum == s_val->RuleNum && cursor->DotNum == s_val->DotNum)
			return 1;
		cursor = cursor->link;
	}
	return 0;
}

//page 12
ty_ptr_item_node GoTo(ty_ptr_item_node IS, sym sym_val)
{
	int r_num, d_num;
	sym SymAfterDot;
	ty_ptr_item_node cursor = NULL;
	ty_ptr_item_node New_Item = NULL;
	ty_ptr_item_node Go_To_Result_List = NULL;
	ty_ptr_item_node i_cursor = NULL;
	ty_ptr_item_node temp_item = NULL;

	cursor = IS;

	while (cursor)
	{
		r_num = cursor->RuleNum;
		d_num = cursor->DotNum;

		if (d_num >= rules[r_num].rleng)
		{
			cursor = cursor->link;
			continue;
		}
		SymAfterDot = rules[r_num].rightside[d_num];

		if (!(SymAfterDot.kind == sym_val.kind && SymAfterDot.no == sym_val.no))
		{
			cursor = cursor->link;
			continue;
		}

		New_Item = (ty_ptr_item_node)malloc(sizeof(type_item));
		New_Item->RuleNum = r_num;
		New_Item->DotNum = d_num + 1;
		New_Item->link = NULL;


		//New_Item가 이미 존재하면 이 아이템은 무시한다.
		if (CheckExistItem(Go_To_Result_List, New_Item))
		{
			free(New_Item);
			cursor = cursor->link;
			continue;
		}

		//NewItemNodePtr를 Go_To_Result_List의 맨 뒤에 붙인다.
		if (Go_To_Result_List == NULL)
			Go_To_Result_List = New_Item;
		else
		{
			temp_item = getLastItem(Go_To_Result_List);
			temp_item->link = New_Item;
			///////////////// p12 빈칸 O ///////////////////////
		}

		cursor = cursor->link;
	}

	if (Go_To_Result_List)
		return closure(Go_To_Result_List);
	else
		return NULL;
}


//page 13
void makeGotoGraph(ty_ptr_item_node IS_O)
{
	int i, j, i_max;
	sym sym_temp;
	goto_set_ptr result = NULL;
	state_node_ptr State_Node_List_Header = NULL;
	state_node_ptr state_cursor = NULL;
	state_node_ptr To_state_node = NULL;
	Arc_node_ptr Arc_List_Header = NULL;
	ty_ptr_item_node To_item_list = NULL;

	State_Node_List_Header = makeStateNode();
	State_Node_List_Header->id = 0;
	State_Node_List_Header->item_cnt = itemListCounter(IS_O);
	State_Node_List_Header->item_start = IS_O;
	State_Node_List_Header->next = NULL;
	Number_Of_States = 1;
	state_cursor = State_Node_List_Header;

	while (state_cursor)
	{
		for (i = 0; i < 2; i++)
		{
			i_max = i ? MaxNonTerminal : MaxTerminal - 1;

			for (j = 0; j < i_max; j++)
			{
				sym_temp.kind = i;
				sym_temp.no = j;

				To_item_list = GoTo(state_cursor->item_start, sym_temp);
				////////////////////////p13 빈칸 O////////////////////////////

				if (To_item_list)
				{
					To_state_node = Add_A_State_Node(State_Node_List_Header, To_item_list);
					Add_An_Arc(&Arc_List_Header, state_cursor->id, To_state_node->id, sym_temp);
					/////////////////////////////p13 빈칸 O///////////////////////////////////////////
				}
			}
		}
		state_cursor = state_cursor->next;
		/////////////////////////p13 빈칸 O ////////////////////////////////
	}

	States_And_Arcs = (goto_set_ptr)malloc(sizeof(goto_set));
	States_And_Arcs->State_Node_List = State_Node_List_Header;
	States_And_Arcs->Arc_list = Arc_List_Header;
}


//page 14
state_node_ptr Add_A_State_Node(state_node_ptr State_Node_List_Header, ty_ptr_item_node To_list)
{
	int Number_Of_Items = 0;
	state_node_ptr cursor = State_Node_List_Header;
	state_node_ptr last_cursor = NULL;
	state_node_ptr new_state_node = NULL;

	Number_Of_Items = itemListCounter(To_list);

	while (cursor)
	{
		if (cursor->item_cnt != Number_Of_Items)
		{
			last_cursor = cursor;
			cursor = cursor->next;
			continue;
		}

		int is_same = is_same_two_itemlists(cursor->item_start, To_list);
		if (is_same)
		{
			deleteTyPtrItemNode(To_list);
			return cursor;
		}

		last_cursor = cursor;
		cursor = cursor->next;
	}

	new_state_node = makeStateNode();
	Number_Of_States++;

	new_state_node->item_cnt = Number_Of_Items;
	new_state_node->item_start = To_list;
	new_state_node->id = last_cursor->id + 1;
	new_state_node->next = NULL;
	last_cursor->next = new_state_node;

	return new_state_node;
}

//page 15
void Add_An_Arc(Arc_node_ptr* Arc_List_Header, int from_num, int to_num, sym Symbol)
{
	Arc_node_ptr Arc_cursor, Arc_last = NULL;
	Arc_node_ptr Arc_new = NULL;
	int same_arc_exists = 0;

	Arc_new = makeArcNode();

	Arc_new->from_state = from_num;
	Arc_new->to_state = to_num;
	Arc_new->gram_sym = Symbol;
	Arc_new->link = NULL;

	if (*Arc_List_Header == NULL)
	{
		*Arc_List_Header = Arc_new;
		NumberOfArcs++;
		return;
	}

	Arc_cursor = *Arc_List_Header;
	while (Arc_cursor)
	{
		if (Arc_cursor->from_state == from_num && Arc_cursor->to_state == to_num && Arc_cursor->gram_sym.kind == Symbol.kind && Arc_cursor->gram_sym.no == Symbol.no)
		{
			same_arc_exists = 1;
			break;
		}
		else
		{
			Arc_last = Arc_cursor;
			Arc_cursor = Arc_cursor->link;
		}
	}

	if (!same_arc_exists)
	{
		Arc_last->link = Arc_new;
		NumberOfArcs++;
	}
	else
		free(Arc_new);
}

//page 16
int is_same_two_itemlists(ty_ptr_item_node list1, ty_ptr_item_node list2)
{
	int I1, I2;
	I1 = itemListCounter(list1);
	I2 = itemListCounter(list2);
	ty_ptr_item_node p1 = list1, p2;

	if (I1 != I2)
		return 0;

	while (p1)
	{
		p2 = list2;
		int p1_exists_in_list2 = 0;

		while (p2)
		{
			if (p1->RuleNum == p2->RuleNum && p1->DotNum == p2->DotNum)
			{
				p1_exists_in_list2 = 1;
				break;
			}
			p2 = p2->link;
		}

		if (!p1_exists_in_list2)
			///////////////////////p16 빈칸  O //////////////////////
			return 0;	// the tow lists are different since an item in list1 dose not eixst in list2.
		p1 = p1->link;
	}
	return 1;
}

//page 17
state_node_ptr makeStateNode(void)
{
	state_node_ptr cursor;

	cursor = (state_node_ptr)malloc(sizeof(state_node));

	cursor->id = -1;
	cursor->item_cnt = 0;
	cursor->item_start = NULL;
	cursor->next = NULL;

	return cursor;
}


Arc_node_ptr makeArcNode(void)
{
	Arc_node_ptr cursor;

	cursor = (Arc_node_ptr)malloc(sizeof(Arc_node));

	cursor->from_state = -1;
	cursor->to_state = -1;
	cursor->gram_sym.kind = -1;
	cursor->gram_sym.no = -1;
	cursor->link = NULL;

	return cursor;
}

int itemListCounter(ty_ptr_item_node IS)
{
	int cnt = 0;
	ty_ptr_item_node cursor = IS;

	while (cursor)
	{
		cnt++;
		cursor = cursor->link;
	}

	return cnt;
}


//page 18

int deleteTyPtrItemNode(ty_ptr_item_node item_list)
{
	ty_ptr_item_node item_next = NULL;
	ty_ptr_item_node item_cursor = item_list->link;

	while (item_cursor)
	{
		item_next = item_cursor->link;
		free(item_cursor);
		item_cursor = item_next;
	}
	free(item_list);
	return 0;
}
void printGotoGraph(goto_set_ptr gsp)
{
	state_node_ptr State_Node_List_Header = gsp->State_Node_List;
	Arc_node_ptr item_list = gsp->Arc_list;
	char str[10];
	FILE* fpw;
	fpw = fopen("goto_graph.txt", "w");

	while (State_Node_List_Header)
	{
		fprintf(fpw, "ID[%2d] (%3d) : ", State_Node_List_Header->id, State_Node_List_Header->item_cnt);
		fitemListPrint(State_Node_List_Header->item_start, fpw);
		State_Node_List_Header = State_Node_List_Header->next;
	}

	printf("\nTotal number of states = %d\n", Number_Of_States);
	fprintf(fpw, "Total number of states = %d\n", Number_Of_States);

	fprintf(fpw, "\nGoto arcs:\nFrom	To	Symbol\n");

	while (item_list)
	{
		fprintf(fpw, "%4d %4d	", item_list->from_state, item_list->to_state);
		if (item_list->gram_sym.kind == 0)
			strcpy(str, Terminals_list[item_list->gram_sym.no].str);
		else
			strcpy(str, Nonterminals_list[item_list->gram_sym.no].str);

		fprintf(fpw, "%s \n", str);

		item_list = item_list->link;
	}

	printf("Total number of arcs = %d\n", NumberOfArcs);
	fprintf(fpw, "Total number of arcs = %d\n", NumberOfArcs);
	fclose(fpw);
}



//page 19

int findToStateNodeId(Arc_node_ptr arc_list, int from_id, sym symbal)
{
	Arc_node_ptr cursor = arc_list;

	while (cursor)
	{
		if ((cursor->from_state == from_id) && (cursor->gram_sym.kind == symbal.kind) && (cursor->gram_sym.no == symbal.no))
			return cursor->to_state;
		cursor = cursor->link;
	}

	return -1;
}

void fitemListPrint(ty_ptr_item_node IS, FILE* fpw)
{
	int i;
	int r_num, d_num;

	ty_ptr_item_node cursor = IS;

	while (cursor)
	{
		r_num = cursor->RuleNum;
		d_num = cursor->DotNum;

		fprintf(fpw, "%s -> ", Nonterminals_list[rules[r_num].leftside.no].str);

		for (i = 0; i < rules[r_num].rleng; i++)
		{
			if (i == d_num)
				fprintf(fpw, ".  ");
			fprintf(fpw, "%s ", rules[r_num].rightside[i].kind ? Nonterminals_list[rules[r_num].rightside[i].no].str :
				Terminals_list[rules[r_num].rightside[i].no].str);
		}

		if (i == d_num)
			fprintf(fpw, ".");
		if (!rules[r_num].rleng)
			fprintf(fpw, " ε ");
		fprintf(fpw, "		");
		cursor = cursor->link;
	}
	fprintf(fpw, "\n");
}


//page 20~21
void Make_Action_Table()
{
	int to_state_id = -1;
	int i = 0;
	state_node_ptr state_cursor = States_And_Arcs->State_Node_List;
	ty_ptr_item_node item_cursor = NULL;
	sym symbol;


	//table 초기화
	Clear_Action_Table();
	while (state_cursor)
	{
		item_cursor = state_cursor->item_start;
		///////////////p20 빈칸 O//////
		while (item_cursor)
		{
			symbol = rules[item_cursor->RuleNum].rightside[item_cursor->DotNum];

			if (rules[item_cursor->RuleNum].rleng > item_cursor->DotNum)
			{
				if (!symbol.kind)
				{
					to_state_id = findToStateNodeId(States_And_Arcs->Arc_list, state_cursor->id, symbol);

					if (to_state_id == -1)	//to state가 없다. 이 경우는 실제로 일어날 수 없다.
					{
						printf("Logic error at Make_Action(1) \n");
						getchar();
					}

					if (Action_Table[state_cursor->id][symbol.no].Kind == 'e')
					{	//초기화로 비어 있는 셀이다. shift action을 넣어줌
						Action_Table[state_cursor->id][symbol.no].Kind = 's';
						Action_Table[state_cursor->id][symbol.no].num = to_state_id;
						//////////p20 빈칸 //////////////
					}
					else		//무언가 이미 들어있음
					{
						if ((Action_Table[state_cursor->id][symbol.no].Kind == 's') && (Action_Table[state_cursor->id][symbol.no].num == to_state_id))
						{		//이미 셀에 동일한 내용이 들어 있음

						}
						else
						{
							printf("Make_Action_Table의 다중값 상황 발생1 \n");
							getchar();
						}
					}

				} // if(!symbol.kind
			}

			else	//dot 이 가장 마지막에 위치
			{
				if (item_cursor->RuleNum == 0)
				{
					if (Action_Table[state_cursor->id][MaxTerminal - 1].Kind == 'e')
					{
						Action_Table[state_cursor->id][MaxTerminal - 1].Kind = 'a';
					}
					else
					{
						printf("Make_Action_Table의 다중값 상황 발생2 \n");
						getchar();
					}
				}
				else	//도트가 마지막인 아이템이므로 이에 대하여 reduction 작업을 수행함.
				{
					for (i = 0; i < MaxTerminal; i++)
					{
						if (FollowTable[rules[item_cursor->RuleNum].leftside.no][i])
						{
							if (Action_Table[state_cursor->id][i].Kind == 'e')
							{
								Action_Table[state_cursor->id][i].Kind = 'r';
								Action_Table[state_cursor->id][i].num = item_cursor->RuleNum;
								////////////////p21 빈칸//////////////
							}
							else
							{		//이미 채워져 있으면,

								if ((Action_Table[state_cursor->id][i].Kind == 'r') && (Action_Table[state_cursor->id][i].num == item_cursor->RuleNum))
								{


								}
								else
								{
									printf("Make_Action_Table의 다중값 상황 발생3\n");
									getchar();
								}
							}
						}
					}
				}
			}
			item_cursor = item_cursor->link;
			////////////p21 빈칸  ///////////////////
		}
		state_cursor = state_cursor->next;
	}
}

//page 22
void print_Action_Table(void)
{
	int i, j;
	FILE* file_ptr = NULL;

	file_ptr = fopen("action_table.txt", "w");
	fprintf(file_ptr, "		\t");

	for (i = 0; i < MaxTerminal; i++)
		fprintf(file_ptr, "%2s\t", Terminals_list[i].str);
	fprintf(file_ptr, "\n");

	for (i = 0; i < Number_Of_States; i++)
	{
		fprintf(file_ptr, "%3d\t", i);
		for (j = 0; j < MaxTerminal; j++)
		{
			fprintf(file_ptr, "%c", Action_Table[i][j].Kind);
			if (Action_Table[i][j].Kind == 's' || Action_Table[i][j].Kind == 'r')
				fprintf(file_ptr, "%2d\t", Action_Table[i][j].num);
			else
				fprintf(file_ptr, "\t");
		}
		fprintf(file_ptr, "\n");
	}

	fclose(file_ptr);
}

void Clear_Action_Table(void)
{
	int i, j;

	for (i = 0; i < Number_Of_States; i++)
	{
		for (j = 0; j < MaxTerminal; j++)
		{
			Action_Table[i][j].Kind = 'e';
			Action_Table[i][j].num = 0;
		}
	}
}

//page 23
void Make_Goto_Table()
{
	int to_state_id = -1;
	int i = 0;
	state_node_ptr state_cursor = States_And_Arcs->State_Node_List;
	ty_ptr_item_node item_cursor = NULL;
	sym symbol;

	Clear_Goto_Table();

	while (state_cursor)
	{
		item_cursor = state_cursor->item_start;
		while (item_cursor)
		{
			symbol = rules[item_cursor->RuleNum].rightside[item_cursor->DotNum];

			//			if (rules[item_cursor->RuleNum].rleng > item_cursor->RuleNum)
			if (rules[item_cursor->RuleNum].rleng > item_cursor->DotNum)
			{	///////////////p23	빈칸 /////////////
				//thre is a grammar symbol after dot
				if (symbol.kind)	//the symbol is a nonterminal
				{
					to_state_id = findToStateNodeId(States_And_Arcs->Arc_list, state_cursor->id, symbol);
					if (to_state_id == -1)
					{
						item_cursor = item_cursor->link;
						continue;
					}

					Goto_Table[state_cursor->id][symbol.no] = to_state_id;
					////////////p23 빈칸/////////////////////////


				}
			}

			item_cursor = item_cursor->link;
		}

		state_cursor = state_cursor->next;
	}
}


// page 24
void Clear_Goto_Table(void)
{
	int i, j;

	for (i = 0; i < MaxNumberOfStates; i++)
	{
		for (j = 0; j < MaxNonTerminal; j++)
		{
			Goto_Table[i][j] = -1;
		}
	}
}

void print_Goto_Table(void)
{
	int i, j;
	FILE* file_ptr = NULL;

	file_ptr = fopen("goto_table.txt", "w");

	fprintf(file_ptr, "   \t");

	for (i = 0; i < MaxNonTerminal; i++)
		fprintf(file_ptr, "%3s\t", Nonterminals_list[i].str);
	fprintf(file_ptr, "\n");

	for (i = 0; i < Number_Of_States; i++)
	{
		fprintf(file_ptr, "%3d\t", i);
		for (j = 0; j < MaxNonTerminal; j++)
		{
			if (Goto_Table[i][j] != -1)
				fprintf(file_ptr, "%3d\t", Goto_Table[i][j]);
			else
				fprintf(file_ptr, " -1\t");
		}
		fprintf(file_ptr, "\n");
	}

	fclose(file_ptr);
}

//page 25, 26 xxxxx




// page 27

void push_state(Ty_Node_Ptr Stack[], int State)
{
	Ty_Node_Ptr NewNode;

	NewNode = (Ty_Node_Ptr)malloc(sizeof(struct nodetype));
	NewNode->state = State;
	Top++;
	Stack[Top] = NewNode;

}

void push_symbol(Ty_Node_Ptr Stack[], Ty_Node_Ptr NodeToPush)
{
	Top++;
	Stack[Top] = NodeToPush;
}

Ty_Node_Ptr pop()
{
	Ty_Node_Ptr rptr;
	if (Top < 0)
	{
		printf("Pop error. Empty stack.\n");
		getchar();
	}

	rptr = Stack[Top];
	Top--;
	return rptr;
}



//page 28
Ty_Node_Ptr Parsing(FILE* fps)
{
	int i, kind, TempState, Finished = 0, State, RuleNo, RuleLeng;
	kind = 0;
	sym NextToken;
	Ty_Node_Ptr Root, NewNode, TempNode;

	push_state(Stack, 0);
	NextToken = get_next_token(fps);

	do
	{
		State = Stack[Top]->state;
		switch (Action_Table[State][NextToken.no].Kind)
		{		///////////p28 빈칸 O///////////
		case 's':
			NewNode = (Ty_Node_Ptr)malloc(sizeof(struct nodetype));
			NewNode->state = -1;
			NewNode->nodesym = NextToken;
			NewNode->child_cnt = 0;
			NewNode->children[0] = NULL;

			push_symbol(Stack, NewNode);

			TempState = Action_Table[State][NextToken.no].num;
			push_state(Stack, TempState);
			NextToken = get_next_token(fps);
			break;
		case 'r':
			NewNode = (Ty_Node_Ptr)malloc(sizeof(struct nodetype));
			NewNode->state = -1;
			RuleNo = Action_Table[State][NextToken.no].num;
			///////////////p28 빈칸 ///////////////
			NewNode->nodesym = rules[RuleNo].leftside;

			RuleLeng = rules[RuleNo].rleng;

			for (i = 0; i < RuleLeng; i++)
			{
				TempNode = pop();
				TempNode = pop();
				NewNode->children[RuleLeng - 1 - i] = TempNode;
				//////////////p28 빈칸 O//////////
			}

			NewNode->child_cnt = RuleLeng;
			NewNode->rule_no_used = RuleNo;
			State = Stack[Top]->state;
			TempState = Goto_Table[State][NewNode->nodesym.no];
			push_symbol(Stack, NewNode);
			push_state(Stack, TempState);
			/////////////////////p28 빈칸 /////////////////

			break;

		case 'a':
			Root = Stack[1];
			return Root; break;

		case 'e':
			printf("Error: Parser is attempting to access an error cell. \n");
			getchar();

			//default: NextToken = get_next_token(fps);
				/////////추가해봄////////////
		}

	} while (1);
}


// page 29

void print_parse_tree(FILE* fout, Ty_Node_Ptr curr, int standard, int first, int child)
{
	int i, j, n = 0;
	if (first != 0)
	{
		for (i = 0; i < standard - 2; i++)
		{
			if (i % 8 == 5)
			{
				n++;
				if (bar[n])
					fprintf(fout, "|");
				else
					fprintf(fout, " ");
			}
			else
				fprintf(fout, " ");
		}
		if (standard != 0)
			fprintf(fout, "--");
	}

	fprintf(fout, "%3s", curr->nodesym.str);

	if (first == child)
		bar[standard / 8] = 0;
	if (curr->nodesym.kind == 0)
		fprintf(fout, "\n");
	else
		fprintf(fout, "-----");

	for (j = 0; j < curr->child_cnt; j++)
	{
		bar[standard / 8 + 1] = 1;
		print_parse_tree(fout, curr->children[j], standard + 8, j, curr->child_cnt - 1);
	}

	return;
}	//void print_pa0rse_tree





/*
void itemListPrint(ty_ptr_item_node IS)
{

}
사용 안해서 빼둠
*/


//그래서 그냥 만듬

ty_ptr_item_node getLastItem(ty_ptr_item_node cs_list)
{
	ty_ptr_item_node TempNode = NULL;
	ty_ptr_item_node curr = cs_list;

	while (1)
	{
		if (curr->link == NULL)
			return curr;
		else
		{
			TempNode = curr;
			curr = curr->link;
		}
	}

}

///////////////강의자료에 없음




/// ///////이 밑으로 다 hw 3 에서 가져온 것들 //////////////////////////
int Compute_first_of_one_nonterminal(sym X)
{
	int i, k, CR = -1;
	int Yi_has_epsilon;
	//	int first_result[Max_symbols + 1]; 원본 코드
	int first_result[MaxSymbols + 1];	//매크로 맞게 내가 바꿈



	for (i = 0; i < MaxTerminal + 2; i++)
		first_result[i] = 0;

Next_Rule:
	CR++;
	if (CR >= totalNumberOfRules)
	{
		for (k = 0; k < MaxTerminal + 1; k++)
			if (first_result[k] == 1)
				FirstTable[X.no][k] = 1;
		FirstTable[X.no][MaxTerminal + 1] = 1;
		return 1;
	}

	if (!(rules[CR].leftside.kind == 1 && rules[CR].leftside.no == X.no))
		goto Next_Rule;

	if (rules[CR].rleng == 0)
	{
		first_result[MaxTerminal] = 1;
		goto Next_Rule;
	}

	i = 0;

Next_Element:
	if (rules[CR].rightside[i].kind == 0)
	{
		first_result[rules[CR].rightside[i].no] = 1;
		goto Next_Rule;
	}

	Yi_has_epsilon = 0;
	if (rules[CR].rightside[i].no != X.no)
	{
		if (FirstTable[rules[CR].rightside[i].no][MaxTerminal + 1] != 1)
			Compute_first_of_one_nonterminal(rules[CR].rightside[i]);

		for (k = 0; k < MaxTerminal + 2; k++)
			if (FirstTable[rules[CR].rightside[i].no][k] == 1)
				first_result[k] = 1;
		if (FirstTable[rules[CR].rightside[i].no][MaxTerminal] == 1)
			Yi_has_epsilon = 1;
	}
	else
	{
		if (first_result[MaxTerminal] == 1)
			Yi_has_epsilon = 1;
	}

	if (Yi_has_epsilon == 0)
		goto Next_Rule;

	if (i == rules[CR].rleng - 1)
	{
		first_result[MaxTerminal] = 1;
		goto Next_Rule;
	}
	else
	{
		i++;
		goto Next_Element;
	}
}


int Compute_first_of_any_string(sym alpha[], int first_result[])
{
	int i, k;
	for (i = 0; i < MaxTerminal + 2; i++)
		first_result[i] = 0; // initialize the first result of alpha

							 // Let alpha be Y0 Y1 ... Yn-1
	i = 0;
	do {
		if (alpha[i].kind == 0) {  // Yi is terminal
			first_result[alpha[i].no] = 1;
			break;
		}
		else if (alpha[i].kind == 1) { // Yi is nonterminal
			for (k = 0; k < MaxTerminal + 2; k++)	 // copy first of Yi to first of alpha
				if (FirstTable[alpha[i].no][k] == 1) first_result[k] = 1;
			if (FirstTable[alpha[i].no][MaxTerminal] == 0)
				break; // first of Yi does not have epsilon.	
			else
				i = i + 1; // move to next Yi.
		}
		else if (alpha[i].kind == -1) {  // end of string mark.
			first_result[MaxTerminal] = 1; // if control reach here, all Yi's have epsilon in its first. Thus alpha has epsilon as first.
			break;
		}
	} while (1);
	return 1; // the first of alpha is passed thru parameter first_result.



}


int Compute_follow_of_one_nonterminal(int idx_NT)
{
	int i, j, k, m;
	//	int first_result[Max_symbols]; // hw3에서 코드
	int first_result[MaxSymbols]; // 매크로 바 
	sym SymString[10];

	for (i = 0; i < totalNumberOfRules; i++) {
		for (j = 0; j < rules[i].rleng; j++)
		{    //  the symbol of index j of the RHS of rule i is to be processed in this iteration
			if (rules[i].rightside[j].kind == 0 || rules[i].rightside[j].no != idx_NT) continue; // skip this symbol j.
																								 // Now, position j has a nonterminal which is equal to idx_NT.
			if (j < rules[i].rleng - 1) {  // there are symbols after position j in RHS of rule i.
				m = 0;
				for (k = j + 1; k < rules[i].rleng; k++, m++) SymString[m] = rules[i].rightside[k];
				SymString[m].kind = -1;  // end of string marker.
				Compute_first_of_any_string(SymString, first_result); // Compute the first of the string after position j of rule i.
				for (k = 0; k < MaxTerminal + 2; k++) // Copy the first symbols of the remaining string to the Follow of idx_NT.
					if (first_result[k] == 1) FollowTable[idx_NT][k] = 1;
			}

			if (j == rules[i].rleng - 1 || first_result[MaxTerminal] == 1) // j is last symbol or first result has epsilon
			{
				if (rules[i].leftside.no == idx_NT) continue; // No need of adding the follow of the left side symbol
				if (FollowTable[rules[i].leftside.no][MaxTerminal] == 0) // We need follow of the left side sym of rule i.
					Compute_follow_of_one_nonterminal(rules[i].leftside.no);
				for (k = 0; k < MaxTerminal + 2; k++) // add follow of left side symbol to follow of idx_NT.
					if (FollowTable[rules[i].leftside.no][k] == 1) FollowTable[idx_NT][k] = 1;
			}
		} // end of for j=0.
	} // end of for i
	FollowTable[idx_NT][MaxTerminal] = 1;  // put the completion mark for this nonterminal.
	return 1;
}

int lookUp_nonterminal(char* str)
{
	int i;

	//	for (i = 0; i < MaxNonterminal; i++)	//hw3 code
	for (i = 0; i < MaxNonTerminal; i++)
		if (strcmp(str, Nonterminals_list[i].str) == 0)
			return i;
	return -1;
}

int lookUp_terminal(char* str)
{
	int i;
	for (i = 0; i < MaxTerminal; i++)
		if (strcmp(str, Terminals_list[i].str) == 0)
			return i;
	return -1;
}

void read_grammar(char* filename)
{
	FILE* fp;
	char line[500];
	char symstr[10];
	char* ret;
	int i, k, n_sym, n_rule, i_leftSymbol, i_rightSymbol, i_right, synkind;
	fp = fopen(filename, "r");
	if (!fp)
	{
		printf("File open error of grammar file.\n");
		getchar();
	}

	ret = fgets(line, 500, fp);
	ret = fgets(line, 500, fp);
	ret = fgets(line, 500, fp);
	i = 0; n_sym = 0;
	do //read nonterminals.
	{
		while (line[i] == ' ' || line[i] == '\t') i++; // skip spaces.
		if (line[i] == '\n') break;
		k = 0;
		while (line[i] != ' ' && line[i] != '\t' && line[i] != '\n')
		{
			symstr[k] = line[i]; i++; k++;
		}
		symstr[k] = '\0';	// a nonterminal string is finished.
		strcpy(Nonterminals_list[n_sym].str, symstr);
		Nonterminals_list[n_sym].kind = 1; //non terminal.
		Nonterminals_list[n_sym].no = n_sym;
		n_sym++;
	} while (1);

	//	MaxNonterminal = n_sym;
	MaxNonTerminal = n_sym;

	i = 0; n_sym = 0;
	ret = fgets(line, 500, fp);	//read terminals line.

	do    //read terminals.
	{
		while (line[i] == ' ' || line[i] == '\t') i++;  //skip spaces.
		if (line[i] == '\n') break;
		k = 0;
		while (line[i] != ' ' && line[i] != '\t' && line[i] != '\n')
		{
			symstr[k] = line[i]; i++; k++;
		}
		symstr[k] = '\0';	//a terminal string is finished
		strcpy(Terminals_list[n_sym].str, symstr);
		Terminals_list[n_sym].kind = 0;	//terminal.
		Terminals_list[n_sym].no = n_sym;
		n_sym++;
	} while (1);
	MaxTerminal = n_sym;

	ret = fgets(line, 500, fp);	//ignore one line
	n_rule = 0;

	do
	{	//reading rules.
		ret = fgets(line, 500, fp);
		if (!ret)
			break;	//no characters were read. So reading rules is terminated.

		//if the line inputed has only white spaces, we should skip this line.
		// this is determined as follows: length==0; or first char is not an alpha
		i = 0;
		if (strlen(line) < 1)
			continue;
		else
		{
			while (line[i] == ' ' || line[i] == '\t') i++; //skip spaces.
			if (!isalpha(line[i]))
				continue;
		}


		//take off left symbol of a rule.
		while (line[i] == ' ' || line[i] == '\t') i++; //skip spaces.
		k = 0;

		while (line[i] != ' ' && line[i] != '\t' && line[i] != '\n')
		{
			symstr[k] = line[i]; i++; k++;
		}
		symstr[k] = '\0'; //a nonterminal string is finished

		i_leftSymbol = lookUp_nonterminal(symstr);
		if (i_leftSymbol < 0)
		{
			printf("Wrong left symbol of a rule.\n");
			getchar();
		}


		//left symbol is stored of the rule.
		rules[n_rule].leftside.kind = 1; rules[n_rule].leftside.no = i_leftSymbol;
		strcpy(rules[n_rule].leftside.str, symstr);
		/////////////////////////////////////

		//by three lines below, we move to first char of first sym of RHS.

		while (line[i] != '>') i++;
		i++;
		while (line[i] == ' ' || line[i] == '\t') i++;


		//collect the symbols of the RHS of the rule. 
		i_right = 0;

		do
		{	//reading symbols of RHS
			k = 0;
			while (i < strlen(line) && (line[i] != ' ' && line[i] != '\t' && line[i] != '\n'))
			{
				symstr[k] = line[i]; i++; k++;
			}
			symstr[k] = '\0';

			if (strcmp(symstr, "epsilon") == 0)	// this is epsilon rule.
			{
				rules[n_rule].rleng = 0;
				//declare that rule is an epsilon rule. //윗줄 수정해야할 수도
				break;
			}


			if (isupper(symstr[0]))
			{		//this is nonterminal
				synkind = 1;
				i_rightSymbol = lookUp_nonterminal(symstr);
			}
			else
			{		//this is terminal
				synkind = 0;
				i_rightSymbol = lookUp_terminal(symstr);
			}

			if (i_rightSymbol < -1)
			{
				printf("Wrong right symbol of a rule.\n");
				getchar();
			}

			rules[n_rule].rightside[i_right].kind = synkind;
			rules[n_rule].rightside[i_right].no = i_rightSymbol;
			strcpy(rules[n_rule].rightside[i_right].str, symstr);
			////////////////////////////////////////////////////////////

			i_right++;

			while (line[i] == ' ' || line[i] == '\t') i++;
			if (i >= strlen(line) || line[i] == '\n') // is needed in case of eof
				break;	//finish reading righthand symbols.
		} while (1);	//loop of reading symbols of RHS.

		rules[n_rule].rleng = i_right;
		////////////////////////////
		n_rule++;
		///////////////////////////////////
	} while (1);	//loop of reading rules.
	totalNumberOfRules = n_rule;
	printf("Total number of rules = %d \n", totalNumberOfRules);
}
