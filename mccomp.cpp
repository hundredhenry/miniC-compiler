#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Host.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <llvm/IR/Constant.h>
#include <llvm/IR/GlobalValue.h>
#include <llvm/IR/GlobalVariable.h>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

#define RED "\e[0;31m"
#define GRN "\e[0;32m"
#define BLU "\e[0;34m"

using namespace llvm;
using namespace llvm::sys;
using namespace std;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE {

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN {
  int type = -100;
  string lexeme;
  int lineNo;
  int columnNo;
};

static string IdentifierStr; // Filled in if IDENT
static int IntVal;           // Filled in if INT_LIT
static bool BoolVal;         // Filled in if BOOL_LIT
static float FloatVal;       // Filled in if FLOAT_LIT
static string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(string lexVal, int tok_type) {
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// getTok - Return the next token from standard input.
static TOKEN getTok() {
  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar)) {
    if (LastChar == '\n' || LastChar == '\r') {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) ||
      (LastChar == '_')) { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true") {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false") {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9]+.
    string NumStr;

    if (LastChar == '.') { // Floating point Number: .[0-9]+
      do {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    } else {
      do { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.') { // Floating point Number: [0-9]+.[0-9]+)
        do {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      } else { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&') {
    NextChar = getc(pFile);
    if (NextChar == '&') { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|') {
    NextChar = getc(pFile);
    if (NextChar == '|') { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
    }
  }

  if (LastChar == '<') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/') { // Could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/') { // Definitely a comment
      do {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return getTok();
    } else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF) {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

static string getTokStr(TOKEN_TYPE type) {
  switch (type) {
  case IDENT:
    return "Name";
  case ASSIGN:
    return "=";
  case LBRA:
    return "{";
  case RBRA:
    return "}";
  case LPAR:
    return "(";
  case RPAR:
    return ")";
  case SC:
    return ";";
  case COMMA:
    return ",";
  case INT_TOK:
    return "int";
  case VOID_TOK:
    return "void";
  case FLOAT_TOK:
    return "float";
  case BOOL_TOK:
    return "bool";
  case EXTERN:
    return "extern";
  case IF:
    return "if";
  case ELSE:
    return "else";
  case WHILE:
    return "while";
  case RETURN:
    return "return";
  case INT_LIT:
    return "INT_LIT";
  case FLOAT_LIT:
    return "FLOAT_LIT";
  case BOOL_LIT:
    return "BOOL_LIT";
  case AND:
    return "&&";
  case OR:
    return "||";
  case PLUS:
    return "+";
  case MINUS:
    return "-";
  case ASTERIX:
    return "*";
  case DIV:
    return "/";
  case MOD:
    return "%";
  case NOT:
    return "!";
  case EQ:
    return "==";
  case NE:
    return "!=";
  case LE:
    return "<=";
  case LT:
    return "<";
  case GE:
    return ">=";
  case GT:
    return ">";
  case EOF_TOK:
    return "EOF";
  case INVALID:
    return "INVALID";
  default:
    return "UNKNOWN";
  }
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static deque<TOKEN> tok_buffer;

static TOKEN getNextToken() {

  if (tok_buffer.size() == 0)
    tok_buffer.push_back(getTok());

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok); }

//===----------------------------------------------------------------------===//
// Helper functions
//===----------------------------------------------------------------------===//

// Checks if a token is in a specified first/follow set vector
static bool contains(vector<TOKEN_TYPE> vec, int tok) {
  if (find(vec.begin(), vec.end(), tok) != vec.end()) {
    return true;
  } else {
    return false;
  }
}

// Matches a token with the expected token type and gets the next token
static bool match(int tok) {
  if (CurTok.type == tok) {
    getNextToken();
    return true;
  } else {
    return false;
  }
}

// Prints an error message and exits the program
static void error(string error_msg, int lineNo, int columnNo) {
  fprintf(stderr, "%d:%d:" RED " error:\e[0m %s\n", lineNo, columnNo,
          error_msg.c_str());
  exit(1);
}

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

/// ASTNode - Base class for all AST nodes.
class ASTNode {
public:
  virtual ~ASTNode() {}
  virtual Value *codegen() = 0;
  virtual string to_string(int indent = 0) const { return ""; };

protected:
  string indentStr(int indent) const { return string(indent, ' '); }
};

/// IntASTNode - Class for integer literals.
class IntASTNode : public ASTNode {
  TOKEN Tok;
  int Val;

public:
  IntASTNode(TOKEN tok, int val) : Tok(tok), Val(val) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    return indentStr(indent) + "<" GRN "IntASTNode\e[0m, " RED +
           ::to_string(Val) + "\e[0m>\n";
  };
};

/// FloatASTNode - Class for float literals.
class FloatASTNode : public ASTNode {
  TOKEN Tok;
  float Val;

public:
  FloatASTNode(TOKEN tok, float val) : Tok(tok), Val(val) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    return indentStr(indent) + "<" GRN "FloatASTNode\e[0m, " RED +
           ::to_string(Val) + "\e[0m>\n";
  };
};

/// BoolASTNode - Class for boolean literals.
class BoolASTNode : public ASTNode {
  TOKEN Tok;
  bool Val;

public:
  BoolASTNode(TOKEN tok, bool val) : Tok(tok), Val(val) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    return indentStr(indent) + "<" GRN "BoolASTNode\e[0m, " RED +
           ::to_string(Val) + "\e[0m>\n";
  };
};

/// VarASTNode - Class for variable declarations.
class VarASTNode : public ASTNode {
  TOKEN Tok;
  TOKEN_TYPE VarType;
  string VarName;
  bool global;

public:
  VarASTNode(TOKEN tok, TOKEN_TYPE type, bool global = false)
      : Tok(tok), VarType(type), VarName(tok.lexeme), global(global) {}
  TOKEN_TYPE getVarType() { return VarType; }
  string getVarName() { return VarName; }
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    return indentStr(indent) + "<" GRN "VarASTNode\e[0m, " RED + VarName +
           "\e[0m: " + RED + getTokStr(VarType) + "\e[0m>\n";
  }
};

/// VarReferenceASTNode - Class for variable references.
class VarReferenceASTNode : public ASTNode {
  TOKEN Tok;
  string VarName;

public:
  VarReferenceASTNode(TOKEN tok) : Tok(tok), VarName(tok.lexeme) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    return indentStr(indent) + "<" GRN "VarReferenceASTNode\e[0m, " RED +
           VarName + "\e[0m>\n";
  };
};

/// UnaryASTNode - Class for unary operators.
class UnaryASTNode : public ASTNode {
  TOKEN Tok;
  int Op;
  unique_ptr<ASTNode> Operand;

public:
  UnaryASTNode(TOKEN tok, unique_ptr<ASTNode> operand)
      : Tok(tok), Op(Tok.type), Operand(std::move(operand)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "UnaryASTNode\e[0m, " RED +
               Tok.lexeme + "\e[0m>\n";
    s += Operand->to_string(indent + 1);

    return s;
  };
};

/// BinaryASTNode - Class for binary operators.
class BinaryASTNode : public ASTNode {
  TOKEN Tok;
  int Op;
  unique_ptr<ASTNode> LHS, RHS;

public:
  BinaryASTNode(TOKEN tok, unique_ptr<ASTNode> lhs, unique_ptr<ASTNode> rhs)
      : Tok(tok), Op(tok.type), LHS(std::move(lhs)), RHS(std::move(rhs)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "BinaryASTNode\e[0m, " RED +
               Tok.lexeme + "\e[0m>\n";
    s += LHS->to_string(indent + 1);
    s += RHS->to_string(indent + 1);

    return s;
  };
};

/// CallASTNode - Class for function calls.
class CallASTNode : public ASTNode {
  TOKEN Tok;
  string FuncName;
  vector<unique_ptr<ASTNode>> Args;

public:
  CallASTNode(TOKEN tok, vector<unique_ptr<ASTNode>> args)
      : Tok(tok), FuncName(tok.lexeme), Args(std::move(args)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "CallASTNode\e[0m, " RED + FuncName +
               "\e[0m>\n";
    s += indentStr(indent) + BLU + "[Arguments]\e[0m\n";
    for (const unique_ptr<ASTNode> &arg : Args) {
      s += arg->to_string(indent + 1);
    }

    return s;
  };
};

/// BlockASTNode - Class for blocks.
class BlockASTNode : public ASTNode {
  vector<unique_ptr<VarASTNode>> LocalDecls;
  vector<unique_ptr<ASTNode>> StmtList;

public:
  BlockASTNode(vector<unique_ptr<VarASTNode>> localDecls,
               vector<unique_ptr<ASTNode>> stmtList)
      : LocalDecls(std::move(localDecls)), StmtList(std::move(stmtList)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "BlockASTNode\e[0m>\n";
    for (const unique_ptr<VarASTNode> &decl : LocalDecls) {
      s += decl->to_string(indent + 1);
    }
    for (const unique_ptr<ASTNode> &stmt : StmtList) {
      s += stmt->to_string(indent + 1);
    }

    return s;
  };
};

/// IfASTNode - Class for if statements.
class IfASTNode : public ASTNode {
  TOKEN Tok;
  unique_ptr<ASTNode> Cond;
  unique_ptr<BlockASTNode> Then, Else;

public:
  IfASTNode(TOKEN tok, unique_ptr<ASTNode> cond, unique_ptr<BlockASTNode> then,
            unique_ptr<BlockASTNode> els)
      : Tok(tok), Cond(std::move(cond)), Then(std::move(then)),
        Else(std::move(els)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "IfASTNode\e[0m>\n";
    s += indentStr(indent) + BLU + "[Condition]\e[0m\n";
    s += Cond->to_string(indent + 1);
    s += indentStr(indent) + BLU + "[Then]\e[0m\n";
    s += Then->to_string(indent + 1);
    if (Else) {
      s += indentStr(indent) + BLU + "[Else]\e[0m\n";
      s += Else->to_string(indent + 1);
    }

    return s;
  };
};

/// WhileASTNode - Class for while statements.
class WhileASTNode : public ASTNode {
  TOKEN Tok;
  unique_ptr<ASTNode> Cond;
  unique_ptr<ASTNode> Stmt;

public:
  WhileASTNode(TOKEN tok, unique_ptr<ASTNode> cond, unique_ptr<ASTNode> stmt)
      : Tok(tok), Cond(std::move(cond)), Stmt(std::move(stmt)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "WhileASTNode\e[0m>\n";
    s += indentStr(indent) + BLU + "[Condition]\e[0m\n";
    s += Cond->to_string(indent + 1);
    s += indentStr(indent) + BLU + "[Statement]\e[0m\n";
    s += Stmt->to_string(indent + 1);

    return s;
  };
};

/// ReturnASTNode - Class for return statements.
class ReturnASTNode : public ASTNode {
  TOKEN Tok;
  unique_ptr<ASTNode> Expr;

public:
  ReturnASTNode(TOKEN tok, unique_ptr<ASTNode> expr)
      : Tok(tok), Expr(std::move(expr)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "ReturnASTNode\e[0m>\n";
    if (Expr) {
      s += Expr->to_string(indent + 1);
    }

    return s;
  };
};

class PrototypeASTNode : public ASTNode {
  TOKEN Tok;
  TOKEN_TYPE FuncType;
  string FuncName;
  vector<unique_ptr<VarASTNode>> Params;

public:
  PrototypeASTNode(TOKEN Tok, TOKEN_TYPE type,
                   vector<unique_ptr<VarASTNode>> params)
      : Tok(Tok), FuncType(type), Params(std::move(params)) {
    FuncName = Tok.lexeme;
  }
  TOKEN getProtoTok() { return Tok; }
  TOKEN_TYPE getProtoType() { return FuncType; }
  string getProtoName() { return FuncName; }
  virtual Function *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "PrototypeASTNode\e[0m, " RED +
               FuncName + "\e[0m: " + RED + getTokStr(FuncType) + "\e[0m>\n";
    for (const unique_ptr<VarASTNode> &arg : Params) {
      s += arg->to_string(indent + 1);
    }

    return s;
  };
};

/// FunctionASTNode - Class for function definitions.
class FunctionASTNode : public ASTNode {
  unique_ptr<PrototypeASTNode> Proto;
  unique_ptr<BlockASTNode> Body;

public:
  FunctionASTNode(unique_ptr<PrototypeASTNode> proto,
                  unique_ptr<BlockASTNode> body)
      : Proto(std::move(proto)), Body(std::move(body)) {}
  virtual Function *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "FunctionASTNode\e[0m>\n";
    s += Proto->to_string(indent + 1);
    s += Body->to_string(indent + 1);

    return s;
  };
};

/// ProgramASTNode - Class for the top-level program.
class ProgramASTNode : public ASTNode {
  vector<unique_ptr<PrototypeASTNode>> Externs;
  vector<unique_ptr<ASTNode>> Decls;

public:
  ProgramASTNode(vector<unique_ptr<PrototypeASTNode>> externs,
                 vector<unique_ptr<ASTNode>> decls)
      : Externs(std::move(externs)), Decls(std::move(decls)) {}
  virtual Value *codegen() override;
  virtual string to_string(int indent = 0) const override {
    string s = indentStr(indent) + "<" GRN "ProgramASTNode\e[0m>\n";
    if (!Externs.empty()) {
      s += indentStr(indent) + BLU + "[Externs]\e[0m\n";
      for (const unique_ptr<PrototypeASTNode> &ext : Externs) {
        s += ext->to_string(indent + 1);
      }
    }
    s += indentStr(indent) + BLU "[Declarations]\e[0m\n";
    for (auto &decl : Decls) {
      s += decl->to_string(indent + 1);
    }

    return s;
  }
};

//===-----------------------------
//-----------------------------------------===//
// First and Follow sets for each production rule
//===----------------------------------------------------------------------===//

// First sets of each production
const vector<TOKEN_TYPE> first_extern_list = {EXTERN};
const vector<TOKEN_TYPE> first_extern_listP = {EXTERN};
const vector<TOKEN_TYPE> first_extern = {EXTERN};
const vector<TOKEN_TYPE> first_decl_list = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                            VOID_TOK};
const vector<TOKEN_TYPE> first_decl_listP = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                             VOID_TOK};
const vector<TOKEN_TYPE> first_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK};
const vector<TOKEN_TYPE> first_type_spec = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                            VOID_TOK};
const vector<TOKEN_TYPE> first_var_type = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_params = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                         VOID_TOK};
const vector<TOKEN_TYPE> first_param_list = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_param_listP = {COMMA};
const vector<TOKEN_TYPE> first_param = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_block = {LBRA};
const vector<TOKEN_TYPE> first_local_decls = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_local_declsP = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_local_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK};
const vector<TOKEN_TYPE> first_stmt_list = {
    NOT,   LPAR, MINUS,    SC,        IF,    RETURN,
    WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_stmt_listP = {
    NOT,   LPAR, MINUS,    SC,        IF,    RETURN,
    WHILE, LBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_stmt = {NOT,      LPAR,      MINUS, SC,
                                       IF,       RETURN,    WHILE, LBRA,
                                       BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_expr_stmt = {
    NOT, LPAR, MINUS, SC, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_while_stmt = {WHILE};
const vector<TOKEN_TYPE> first_if_stmt = {IF};
const vector<TOKEN_TYPE> first_else_stmt = {ELSE};
const vector<TOKEN_TYPE> first_return_stmt = {RETURN};
const vector<TOKEN_TYPE> first_expr = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                       FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_logical_or = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                             FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_logical_orP = {OR};
const vector<TOKEN_TYPE> first_logical_and = {
    NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_logical_andP = {AND};
const vector<TOKEN_TYPE> first_equality = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                           FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_equalityP = {EQ, NE};
const vector<TOKEN_TYPE> first_relational = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                             FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_relationalP = {LT, LE, GT, GE};
const vector<TOKEN_TYPE> first_additive = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                           FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_additiveP = {PLUS, MINUS};
const vector<TOKEN_TYPE> first_multiplicative = {
    NOT, LPAR, MINUS, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_multiplicativeP = {MOD, ASTERIX, DIV};
const vector<TOKEN_TYPE> first_factor = {LPAR, BOOL_LIT, FLOAT_LIT, IDENT,
                                         INT_LIT};
const vector<TOKEN_TYPE> first_reference = {BOOL_LIT, FLOAT_LIT, IDENT,
                                            INT_LIT};
const vector<TOKEN_TYPE> first_referenceP = {LPAR};
const vector<TOKEN_TYPE> first_literal = {BOOL_LIT, FLOAT_LIT, INT_LIT};
const vector<TOKEN_TYPE> first_args = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                       FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_arg_list = {NOT,       LPAR,  MINUS,  BOOL_LIT,
                                           FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> first_arg_listP = {COMMA};

// Follow sets of each production
const vector<TOKEN_TYPE> follow_extern_listP = {BOOL_TOK, FLOAT_TOK, INT_TOK,
                                                VOID_TOK};
const vector<TOKEN_TYPE> follow_decl = {BOOL_TOK, FLOAT_TOK, INT_TOK, VOID_TOK,
                                        EOF_TOK};
const vector<TOKEN_TYPE> follow_decl_listP = {EOF_TOK};
const vector<TOKEN_TYPE> follow_params = {RPAR};
const vector<TOKEN_TYPE> follow_param_listP = {RPAR};
const vector<TOKEN_TYPE> follow_local_decls = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_local_declsP = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_stmt_list = {RBRA};
const vector<TOKEN_TYPE> follow_stmt_listP = {RBRA};
const vector<TOKEN_TYPE> follow_expr_stmt = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_else_stmt = {
    NOT,  LPAR, MINUS,    SC,        IF,    RETURN, WHILE,
    LBRA, RBRA, BOOL_LIT, FLOAT_LIT, IDENT, INT_LIT};
const vector<TOKEN_TYPE> follow_expr = {RPAR, COMMA, SC};
const vector<TOKEN_TYPE> follow_logical_or = {RPAR, COMMA, SC};
const vector<TOKEN_TYPE> follow_logical_orP = {RPAR, COMMA, SC};
const vector<TOKEN_TYPE> follow_logical_andP = {RPAR, COMMA, SC, OR};
const vector<TOKEN_TYPE> follow_equalityP = {AND, RPAR, COMMA, SC, OR};
const vector<TOKEN_TYPE> follow_relationalP = {NE, AND, RPAR, COMMA,
                                               SC, EQ,  OR};
const vector<TOKEN_TYPE> follow_additiveP = {NE, AND, RPAR, COMMA, SC, LT,
                                             LE, EQ,  GT,   GE,    OR};
const vector<TOKEN_TYPE> follow_multiplicativeP = {
    NE, AND, RPAR, PLUS, COMMA, MINUS, SC, LT, LE, EQ, GT, GE, OR};
const vector<TOKEN_TYPE> follow_referenceP = {
    NE,  MOD, AND, RPAR, ASTERIX, PLUS, COMMA, MINUS,
    DIV, SC,  LT,  LE,   EQ,      GT,   GE,    OR};
const vector<TOKEN_TYPE> follow_args = {RPAR};
const vector<TOKEN_TYPE> follow_arg_listP = {RPAR};

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

// Function prototypes
vector<unique_ptr<ASTNode>> p_arg_listP(vector<unique_ptr<ASTNode>> &arg_list);
vector<unique_ptr<ASTNode>> p_arg_list();
vector<unique_ptr<ASTNode>> p_args();
unique_ptr<ASTNode> p_literal();
vector<unique_ptr<ASTNode>> p_referenceP();
unique_ptr<ASTNode> p_reference();
unique_ptr<ASTNode> p_factor();
unique_ptr<ASTNode> p_unary();
unique_ptr<ASTNode> p_multiplicativeP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_multiplicative();
unique_ptr<ASTNode> p_additiveP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_additive();
unique_ptr<ASTNode> p_relationalP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_relational();
unique_ptr<ASTNode> p_equalityP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_equality();
unique_ptr<ASTNode> p_logical_andP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_logical_and();
unique_ptr<ASTNode> p_logical_orP(unique_ptr<ASTNode> lhs);
unique_ptr<ASTNode> p_logical_or();
unique_ptr<ASTNode> p_expr();
unique_ptr<ASTNode> p_return_stmt();
unique_ptr<BlockASTNode> p_else_stmt();
unique_ptr<ASTNode> p_if_stmt();
unique_ptr<ASTNode> p_while_stmt();
unique_ptr<ASTNode> p_expr_stmt();
unique_ptr<ASTNode> p_stmt();
vector<unique_ptr<ASTNode>>
p_stmt_listP(vector<unique_ptr<ASTNode>> &stmt_list);
vector<unique_ptr<ASTNode>> p_stmt_list();
unique_ptr<VarASTNode> p_local_decl();
vector<unique_ptr<VarASTNode>>
p_local_declsP(vector<unique_ptr<VarASTNode>> &local_decls);
vector<unique_ptr<VarASTNode>> p_local_decls();
unique_ptr<BlockASTNode> p_block();
unique_ptr<VarASTNode> p_param();
vector<unique_ptr<VarASTNode>>
p_param_listP(vector<unique_ptr<VarASTNode>> &param_list);
vector<unique_ptr<VarASTNode>> p_param_list();
vector<unique_ptr<VarASTNode>> p_params();
TOKEN_TYPE p_var_type();
TOKEN_TYPE p_type_spec();
unique_ptr<ASTNode> p_decl();
vector<unique_ptr<ASTNode>>
p_decl_listP(vector<unique_ptr<ASTNode>> &decl_list);
vector<unique_ptr<ASTNode>> p_decl_list();
unique_ptr<PrototypeASTNode> p_extern();
vector<unique_ptr<PrototypeASTNode>>
p_extern_listP(vector<unique_ptr<PrototypeASTNode>> &extern_list);
vector<unique_ptr<PrototypeASTNode>> p_extern_list();
unique_ptr<ProgramASTNode> p_program();

// arg_list' -> "," expr arg_list' | ϵ
vector<unique_ptr<ASTNode>> p_arg_listP(vector<unique_ptr<ASTNode>> &arg_list) {
  if (!match(COMMA)) {
    if (contains(follow_arg_listP, CurTok.type)) {
      return std::move(arg_list);
    } else {
      error("Expected ',' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<ASTNode> expr = p_expr();
  arg_list.push_back(std::move(expr));

  return p_arg_listP(arg_list);
}

// arg_list -> expr arg_list'
vector<unique_ptr<ASTNode>> p_arg_list() {
  vector<unique_ptr<ASTNode>> arg_list;
  unique_ptr<ASTNode> expr = p_expr();
  arg_list.push_back(std::move(expr));

  return p_arg_listP(arg_list);
}

// args -> arg_list | ϵ
vector<unique_ptr<ASTNode>> p_args() {
  if (!contains(first_args, CurTok.type)) {
    if (contains(follow_args, CurTok.type)) {
      return {}; // No arguments
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }

  return p_arg_list();
}

// literal -> INT_LIT | FLOAT_LIT | BOOL_LIT
unique_ptr<ASTNode> p_literal() {
  TOKEN literal = CurTok;

  if (match(INT_LIT)) {
    return make_unique<IntASTNode>(literal, IntVal);
  } else if (match(FLOAT_LIT)) {
    return make_unique<FloatASTNode>(literal, FloatVal);
  } else if (match(BOOL_LIT)) {
    return make_unique<BoolASTNode>(literal, BoolVal);
  } else {
    error("Expected literal but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
    return nullptr;
  }
}

// reference' -> "(" args ")" | ϵ
unique_ptr<ASTNode> p_referenceP(TOKEN &tok) {
  if (!match(LPAR)) {
    if (contains(follow_referenceP, CurTok.type)) {
      return make_unique<VarReferenceASTNode>(tok);
    } else {
      error("Expected '(' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  vector<unique_ptr<ASTNode>> args = p_args();
  if (!match(RPAR)) {
    error("Expected ')' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }

  return make_unique<CallASTNode>(tok, std::move(args));
}

// reference -> IDENT reference' | literal
unique_ptr<ASTNode> p_reference() {
  TOKEN temp = CurTok;
  if (!match(IDENT)) {
    if (contains(first_literal, CurTok.type)) {
      return p_literal();
    } else {
      error("Expected identifier but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }

  return p_referenceP(temp);
}

// factor -> "(" expr ")" | reference
unique_ptr<ASTNode> p_factor() {
  if (!match(LPAR)) {
    if (contains(first_reference, CurTok.type)) {
      return p_reference();
    } else {
      error("Expected '(' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<ASTNode> expr = p_expr();
  if (!match(RPAR)) {
    error("Expected ')' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }

  return expr;
}

// unary -> "-" unary | "!" unary | factor
unique_ptr<ASTNode> p_unary() {
  TOKEN unaryOp = CurTok;
  if (!match(MINUS) && !match(NOT)) {
    if (contains(first_factor, CurTok.type)) {
      return p_factor();
    } else {
      error("Expected '-' or '!' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }

  return make_unique<UnaryASTNode>(unaryOp, p_unary());
}

// multiplicative' -> "*" unary multiplicative' | "/" unary multiplicative' |
// "%" unary multiplicative' | ϵ
unique_ptr<ASTNode> p_multiplicativeP(unique_ptr<ASTNode> lhs) {
  TOKEN multiplicativeOp = CurTok;
  if (!match(ASTERIX) && !match(DIV) && !match(MOD)) {
    if (contains(follow_multiplicativeP, CurTok.type)) {
      return lhs;
    } else {
      error("Expected '*', '/', or '%' but found " + CurTok.lexeme,
            CurTok.lineNo, CurTok.columnNo);
    }
  }
  unique_ptr<BinaryASTNode> multiplicativeExpr =
      make_unique<BinaryASTNode>(multiplicativeOp, std::move(lhs), p_unary());

  return p_multiplicativeP(std::move(multiplicativeExpr));
}

// multiplicative -> unary multiplicative'
unique_ptr<ASTNode> p_multiplicative() {
  unique_ptr<ASTNode> unary = p_unary();

  return p_multiplicativeP(std::move(unary));
}

// additive' -> "+" multiplicative additive' | "-" multiplicative additive' | ϵ
unique_ptr<ASTNode> p_additiveP(unique_ptr<ASTNode> lhs) {
  TOKEN additiveOp = CurTok;
  if (!match(PLUS) && !match(MINUS)) {
    if (contains(follow_additiveP, CurTok.type)) {
      return lhs;
    } else {
      error("Expected '+' or '-' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<BinaryASTNode> additiveExpr = make_unique<BinaryASTNode>(
      additiveOp, std::move(lhs), p_multiplicative());

  return p_additiveP(std::move(additiveExpr));
}

// additive -> multiplicative additive'
unique_ptr<ASTNode> p_additive() {
  unique_ptr<ASTNode> multiplicativeExpr = p_multiplicative();

  return p_additiveP(std::move(multiplicativeExpr));
}

// relational' -> "<=" additive relational' | "<" additive relational' | ">="
// additive relational' | ">" additive relational' | ϵ
unique_ptr<ASTNode> p_relationalP(unique_ptr<ASTNode> lhs) {
  TOKEN relationalOp = CurTok;
  if (!match(LE) && !match(LT) && !match(GE) && !match(GT)) {
    if (contains(follow_relationalP, CurTok.type)) {
      return lhs;
    } else {
      error("Expected '<=', '<', '>=' or '>' but found " + CurTok.lexeme,
            CurTok.lineNo, CurTok.columnNo);
    }
  }
  unique_ptr<BinaryASTNode> relationalExpr =
      make_unique<BinaryASTNode>(relationalOp, std::move(lhs), p_additive());

  return p_relationalP(std::move(relationalExpr));
}

// relational -> additive relational'
unique_ptr<ASTNode> p_relational() {
  unique_ptr<ASTNode> additiveExpr = p_additive();

  return p_relationalP(std::move(additiveExpr));
}

// equality' -> "==" relational equality' | "!=" relational equality' | ϵ
unique_ptr<ASTNode> p_equalityP(unique_ptr<ASTNode> lhs) {
  TOKEN equalityOp = CurTok;
  if (!match(EQ) && !match(NE)) {
    if (contains(follow_equalityP, CurTok.type)) {
      return lhs;
    } else {
      error("Expected '==' or '!=' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<BinaryASTNode> equalityExpr =
      make_unique<BinaryASTNode>(equalityOp, std::move(lhs), p_relational());

  return p_equalityP(std::move(equalityExpr));
}

// equality -> relational equality'
unique_ptr<ASTNode> p_equality() {
  unique_ptr<ASTNode> relationalExpr = p_relational();

  return p_equalityP(std::move(relationalExpr));
}

// logical_and' -> "&&" equality logical_and' | ϵ
unique_ptr<ASTNode> p_logical_andP(unique_ptr<ASTNode> lhs) {
  TOKEN logicalAndOp = CurTok;
  if (!match(AND)) {
    if (contains(follow_logical_andP, CurTok.type)) {
      return lhs;
    } else {
      error("Expected '&&' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<BinaryASTNode> logicalAndExpr =
      make_unique<BinaryASTNode>(logicalAndOp, std::move(lhs), p_equality());
  return p_logical_andP(std::move(logicalAndExpr));
}

// logical_and -> equality logical_and'
unique_ptr<ASTNode> p_logical_and() {
  unique_ptr<ASTNode> equalityExpr = p_equality();

  return p_logical_andP(std::move(equalityExpr));
}

// logical_or' -> "||" logical_and logical_or' | ϵ
unique_ptr<ASTNode> p_logical_orP(unique_ptr<ASTNode> lhs) {
  TOKEN logicalOrOp = CurTok;
  if (!match(OR)) {
    if (contains(follow_logical_orP, CurTok.type)) {
      return lhs;
    } else {
      error("Expected '||' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<BinaryASTNode> logicalOrExpr =
      make_unique<BinaryASTNode>(logicalOrOp, std::move(lhs), p_logical_and());

  return p_logical_orP(std::move(logicalOrExpr));
}

// logical_or -> logical_and logical_or'
unique_ptr<ASTNode> p_logical_or() {
  unique_ptr<ASTNode> logicalAndExpr = p_logical_and();

  return p_logical_orP(std::move(logicalAndExpr));
}

// expr -> IDENT "=" expr | logical_or
unique_ptr<ASTNode> p_expr() {
  TOKEN temp = CurTok;
  TOKEN assignOp = getNextToken();
  if (!(temp.type == IDENT) || !match(ASSIGN)) {
    if (contains(first_logical_or, temp.type)) {
      putBackToken(CurTok);
      CurTok = temp;
      return p_logical_or();
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<VarReferenceASTNode> var = make_unique<VarReferenceASTNode>(temp);
  unique_ptr<ASTNode> expr = p_expr();

  return make_unique<BinaryASTNode>(assignOp, std::move(var), std::move(expr));
}

// return_stmt -> "return" expr_stmt
unique_ptr<ASTNode> p_return_stmt() {
  TOKEN returnTok = CurTok;
  if (!match(RETURN)) {
    error("Expected 'return' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  unique_ptr<ASTNode> exprStmt = p_expr_stmt();

  return make_unique<ReturnASTNode>(returnTok, std::move(exprStmt));
}

// else_stmt -> "else" block | ϵ
unique_ptr<BlockASTNode> p_else_stmt() {
  TOKEN elseTok = CurTok;
  if (!match(ELSE)) {
    if (contains(follow_else_stmt, CurTok.type)) {
      return nullptr;
    } else {
      error("Expected 'else' but found " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<BlockASTNode> block = p_block();

  return block;
}

// if_stmt -> "if" "(" expr ")" block else_stmt
unique_ptr<ASTNode> p_if_stmt() {
  TOKEN ifTok = CurTok;
  if (!match(IF)) {
    error("Expected 'if' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  if (!match(LPAR)) {
    error("Expected '(' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  unique_ptr<ASTNode> cond = p_expr();
  if (!match(RPAR)) {
    error("Expected ')' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  unique_ptr<BlockASTNode> thenBlock = p_block();
  unique_ptr<BlockASTNode> elseStmt = p_else_stmt();

  return make_unique<IfASTNode>(ifTok, std::move(cond), std::move(thenBlock),
                                std::move(elseStmt));
}

// while_stmt -> "while" "(" expr ")" stmt
unique_ptr<ASTNode> p_while_stmt() {
  TOKEN whileTok = CurTok;
  if (!match(WHILE)) {
    error("Expected 'while' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  if (!match(LPAR)) {
    error("Expected '(' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  unique_ptr<ASTNode> expr = p_expr();
  if (!match(RPAR)) {
    error("Expected ')' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  unique_ptr<ASTNode> stmt = p_stmt();

  return make_unique<WhileASTNode>(whileTok, std::move(expr), std::move(stmt));
}

// expr_stmt -> expr ";" | ";"
unique_ptr<ASTNode> p_expr_stmt() {
  if (!contains(first_expr, CurTok.type)) {
    if (match(SC)) {
      return nullptr;
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<ASTNode> expr = p_expr();
  if (!match(SC)) {
    error("Expected ';' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }

  return expr;
}

// stmt -> expr_stmt | block | if_stmt | while_stmt | return_stmt
unique_ptr<ASTNode> p_stmt() {
  if (contains(first_expr_stmt, CurTok.type)) {
    return p_expr_stmt();
  } else if (contains(first_block, CurTok.type)) {
    return p_block();
  } else if (contains(first_if_stmt, CurTok.type)) {
    return p_if_stmt();
  } else if (contains(first_while_stmt, CurTok.type)) {
    return p_while_stmt();
  } else if (contains(first_return_stmt, CurTok.type)) {
    return p_return_stmt();
  } else {
    error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
}

// stmt_list' -> stmt stmt_list' | ϵ
vector<unique_ptr<ASTNode>>
p_stmt_listP(vector<unique_ptr<ASTNode>> &stmt_list) {
  if (!contains(first_stmt, CurTok.type)) {
    if (contains(follow_stmt_listP, CurTok.type)) {
      return std::move(stmt_list);
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<ASTNode> stmt = p_stmt();
  stmt_list.push_back(std::move(stmt));

  return p_stmt_listP(stmt_list);
}

// stmt_list -> stmt stmt_list'
vector<unique_ptr<ASTNode>> p_stmt_list() {
  vector<unique_ptr<ASTNode>> stmt_list;
  unique_ptr<ASTNode> stmt = p_stmt();
  stmt_list.push_back(std::move(stmt));

  return p_stmt_listP(stmt_list);
}

// local_decl -> var_type IDENT ";"
unique_ptr<VarASTNode> p_local_decl() {
  TOKEN_TYPE varType = p_var_type();
  TOKEN varName = CurTok;
  if (!match(IDENT)) {
    error("Expected identifier but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  if (!match(SC)) {
    error("Expected ';' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }

  return make_unique<VarASTNode>(varName, varType);
}

// local_decls' -> local_decl local_decls' | ϵ
vector<unique_ptr<VarASTNode>>
p_local_declsP(vector<unique_ptr<VarASTNode>> &local_decls) {
  if (!contains(first_local_decl, CurTok.type)) {
    if (contains(follow_local_declsP, CurTok.type)) {
      return std::move(local_decls);
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<VarASTNode> localDecl = p_local_decl();
  local_decls.push_back(std::move(localDecl));

  return p_local_declsP(local_decls);
}

// local_decls -> local_decls'
vector<unique_ptr<VarASTNode>> p_local_decls() {
  vector<unique_ptr<VarASTNode>> local_decls;

  return p_local_declsP(local_decls);
}

// block -> "{" local_decls stmt_list "}"
unique_ptr<BlockASTNode> p_block() {
  if (!match(LBRA)) {
    error("Expected '{' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  vector<unique_ptr<VarASTNode>> localDecls = p_local_decls();
  vector<unique_ptr<ASTNode>> stmtList = p_stmt_list();
  if (!match(RBRA)) {
    error("Expected '}' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }

  return make_unique<BlockASTNode>(std::move(localDecls), std::move(stmtList));
}

// param -> var_type IDENT
unique_ptr<VarASTNode> p_param() {
  TOKEN_TYPE varType = p_var_type();
  TOKEN varName = CurTok;
  if (!match(IDENT)) {
    error("Expected identifier but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }

  return make_unique<VarASTNode>(varName, varType);
}

// param_list' -> "," param param_list' | ϵ
vector<unique_ptr<VarASTNode>>
p_param_listP(vector<unique_ptr<VarASTNode>> &param_list) {
  if (!match(COMMA)) {
    if (contains(follow_param_listP, CurTok.type)) {
      return std::move(param_list);
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<VarASTNode> param = p_param();
  param_list.push_back(std::move(param));

  return p_param_listP(param_list);
}

// param_list -> param param_list'
vector<unique_ptr<VarASTNode>> p_param_list() {
  vector<unique_ptr<VarASTNode>> param_list;
  unique_ptr<VarASTNode> param = p_param();
  param_list.push_back(std::move(param));

  return p_param_listP(param_list);
}

// params -> param_list | "void" | ϵ
vector<unique_ptr<VarASTNode>> p_params() {
  if (!contains(first_params, CurTok.type)) {
    if (contains(follow_params, CurTok.type)) {
      return {}; // Void, no parameters
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  if (match(VOID_TOK)) {
    return {};
  }

  return p_param_list();
}

// var_type -> "int" | "float" | "bool"
TOKEN_TYPE p_var_type() {
  if (match(INT_TOK)) {
    return INT_TOK;
  } else if (match(FLOAT_TOK)) {
    return FLOAT_TOK;
  } else if (match(BOOL_TOK)) {
    return BOOL_TOK;
  } else {
    error("Expected 'int', 'float', or 'bool' but found " + CurTok.lexeme,
          CurTok.lineNo, CurTok.columnNo);
  }
}

// type_spec -> var_type | "void"
TOKEN_TYPE p_type_spec() {
  if (contains(first_var_type, CurTok.type)) {
    return p_var_type();
  } else if (match(VOID_TOK)) {
    return VOID_TOK;
  } else {
    error("Expected 'int', 'float', 'bool', or 'void' but found " +
              CurTok.lexeme,
          CurTok.lineNo, CurTok.columnNo);
  }
}

// decl -> var_type IDENT ";" | type_spec IDENT "(" params ")" block
unique_ptr<ASTNode> p_decl() {
  if (!contains(first_var_type, CurTok.type) &&
      !contains(first_type_spec, CurTok.type)) {
    error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  TOKEN_TYPE declType = p_type_spec();
  TOKEN declName = CurTok;
  if (!match(IDENT)) {
    error("Expected identifier but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  if (match(SC)) {
    if (declType == VOID_TOK) {
      error("Variable declaration cannot have type 'void'", CurTok.lineNo,
            CurTok.columnNo);
    }
    return make_unique<VarASTNode>(declName, declType, true);
  }
  if (!match(LPAR)) {
    error("Expected '(' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  vector<unique_ptr<VarASTNode>> params = p_params();
  if (!match(RPAR)) {
    error("Expected ')' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  unique_ptr<PrototypeASTNode> proto =
      make_unique<PrototypeASTNode>(declName, declType, std::move(params));
  unique_ptr<BlockASTNode> block = p_block();

  return make_unique<FunctionASTNode>(std::move(proto), std::move(block));
}

// decl_list' -> decl decl_list' | ϵ
vector<unique_ptr<ASTNode>>
p_decl_listP(vector<unique_ptr<ASTNode>> &decl_list) {
  if (!contains(first_decl, CurTok.type)) {
    if (contains(follow_decl_listP, CurTok.type)) {
      return std::move(decl_list);
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<ASTNode> decl = p_decl();
  decl_list.push_back(std::move(decl));

  return p_decl_listP(decl_list);
}

// decl_list -> decl decl_list'
vector<unique_ptr<ASTNode>> p_decl_list() {
  vector<unique_ptr<ASTNode>> decl_list;
  unique_ptr<ASTNode> decl = p_decl();
  decl_list.push_back(std::move(decl));

  return p_decl_listP(decl_list);
}

// extern -> "extern" type_spec IDENT "(" params ")" ";"
unique_ptr<PrototypeASTNode> p_extern() {
  if (!match(EXTERN)) {
    error("Expected 'extern' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  TOKEN_TYPE externType = p_type_spec();
  TOKEN externName = CurTok;
  if (!match(IDENT)) {
    error("Expected identifier but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  if (!match(LPAR)) {
    error("Expected '(' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  vector<unique_ptr<VarASTNode>> params = p_params();
  if (!match(RPAR)) {
    error("Expected ')' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
  if (!match(SC)) {
    error("Expected ';' but found " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }

  return make_unique<PrototypeASTNode>(externName, externType,
                                       std::move(params));
}

// extern_list' -> extern extern_list' | ϵ
vector<unique_ptr<PrototypeASTNode>>
p_extern_listP(vector<unique_ptr<PrototypeASTNode>> &extern_list) {
  if (!contains(first_extern, CurTok.type)) {
    if (contains(follow_extern_listP, CurTok.type)) {
      return std::move(extern_list);
    } else {
      error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
            CurTok.columnNo);
    }
  }
  unique_ptr<PrototypeASTNode> externDecl = p_extern();
  extern_list.push_back(std::move(externDecl));

  return p_extern_listP(extern_list);
}

// extern_list -> extern extern_list'
vector<unique_ptr<PrototypeASTNode>> p_extern_list() {
  vector<unique_ptr<PrototypeASTNode>> extern_list;

  return p_extern_listP(extern_list);
}

// program -> extern_list decl_list | decl_list
unique_ptr<ProgramASTNode> p_program() {
  if (contains(first_extern_list, CurTok.type)) {
    vector<unique_ptr<PrototypeASTNode>> externs = p_extern_list();
    vector<unique_ptr<ASTNode>> decls = p_decl_list();

    return make_unique<ProgramASTNode>(std::move(externs), std::move(decls));
  } else if (contains(first_decl_list, CurTok.type)) {
    vector<unique_ptr<PrototypeASTNode>> externs;
    vector<unique_ptr<ASTNode>> decls = p_decl_list();

    return make_unique<ProgramASTNode>(std::move(externs), std::move(decls));
  } else {
    error("Found invalid token " + CurTok.lexeme, CurTok.lineNo,
          CurTok.columnNo);
  }
}

static unique_ptr<ProgramASTNode> parser() {
  getNextToken(); // Consume EOF
  unique_ptr<ProgramASTNode> program = p_program();

  if (CurTok.type == EOF_TOK) {
    fprintf(stderr, "Parsing Successful\n");
    return std::move(program);
  } else {
    fprintf(stderr, "Parsing Failed\n");
    return nullptr;
  }
}

//===----------------------------------------------------------------------===//
// `Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static unique_ptr<Module> TheModule;
static vector<map<string, AllocaInst *>> NamedValues;
static map<string, GlobalVariable *> GlobalNamedValues;

static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
                                          const string &VarName,
                                          Type *VarType) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(),
                   TheFunction->getEntryBlock().begin());
  return TmpB.CreateAlloca(VarType, 0, VarName.c_str());
}

static AllocaInst *findVar(const string &name) {
  // Search for variable from innermost scope to outermost scope
  for (auto it = NamedValues.rbegin(); it != NamedValues.rend(); ++it) {
    if (it->find(name) != it->end()) {
      return (*it)[name];
    }
  }

  return nullptr;
}

static Type *getLLVMType(TOKEN_TYPE type) {
  switch (type) {
  case BOOL_TOK:
    return Type::getInt1Ty(TheContext);
  case FLOAT_TOK:
    return Type::getFloatTy(TheContext);
  case INT_TOK:
    return Type::getInt32Ty(TheContext);
  case VOID_TOK:
    return Type::getVoidTy(TheContext);
  default:
    return nullptr;
  }
}

static Value *loadIfVar(Value *val) {
  if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(val)) {
    return Builder.CreateLoad(allocaInst->getAllocatedType(), allocaInst,
                              "loadtmp");
  } else if (GlobalVariable *globalVar = dyn_cast<GlobalVariable>(val)) {
    return Builder.CreateLoad(globalVar->getValueType(), globalVar,
                              "loadglobaltmp");
  }

  return val;
}

static Value *castToBool(Value *val) {
  if (val->getType()->isIntegerTy(32)) {
    return Builder.CreateICmpNE(val, ConstantInt::get(TheContext, APInt(32, 0)),
                                "booltmp");
  } else if (val->getType()->isFloatTy()) {
    return Builder.CreateFPToUI(val, Type::getInt1Ty(TheContext), "booltmp");
  }

  return val;
}

static Value *castToInt(Value *val) {
  if (val->getType()->isIntegerTy(1)) {
    return Builder.CreateZExt(val, Type::getInt32Ty(TheContext), "inttmp");
  } else if (val->getType()->isFloatTy()) {
    return Builder.CreateFPToSI(val, Type::getInt32Ty(TheContext), "inttmp");
  }

  return val;
}

static Value *castToFloat(Value *val) {
  if (val->getType()->isIntegerTy(1)) {
    return Builder.CreateUIToFP(val, Type::getFloatTy(TheContext), "floattmp");
  } else if (val->getType()->isIntegerTy(32)) {
    return Builder.CreateSIToFP(val, Type::getFloatTy(TheContext), "floattmp");
  }

  return val;
}

static Value *cast(Value *val, Type *type) {
  if (val->getType() == type) {
    return val; // No need to cast
  }
  if (type->isFloatTy()) {
    return castToFloat(val); // Can cast boolean or int to float
  } else if (type->isIntegerTy(32)) {
    if (val->getType()->isFloatTy()) {
      printf("Cannot narrow float to int\n");
      return nullptr; // Error, cannot narrow float to int
    }
    return castToInt(val); // Can cast boolean to int
  } else {
    printf("Narrowing int or float to bool\n");
    return nullptr; // Error, cannot narrow int or float to bool
  }
}

static Type *priorityType(Type *lhs, Type *rhs) {
  if (lhs->isFloatTy() || rhs->isFloatTy()) {
    return Type::getFloatTy(TheContext);
  } else if (lhs->isIntegerTy(32) || rhs->isIntegerTy(32)) {
    return Type::getInt32Ty(TheContext);
  } else {
    return Type::getInt1Ty(TheContext);
  }
}

Value *IntASTNode::codegen() {
  return ConstantInt::get(TheContext, APInt(32, Val, true));
}

Value *FloatASTNode::codegen() {
  return ConstantFP::get(TheContext, APFloat(Val));
}

Value *BoolASTNode::codegen() {
  return ConstantInt::get(TheContext, APInt(1, Val, false));
}

Value *VarASTNode::codegen() {
  Type *type = getLLVMType(VarType);

  if (global) {
    if (GlobalNamedValues.find(VarName) != GlobalNamedValues.end()) {
      error("Global variable " + VarName + " has an existing definition", Tok.lineNo,
            Tok.columnNo);
    }
    TheModule->getOrInsertGlobal(VarName, type);
    GlobalVariable *globalVar = TheModule->getNamedGlobal(VarName);
    globalVar->setInitializer(Constant::getNullValue(type));
    globalVar->setLinkage(GlobalValue::CommonLinkage);
    globalVar->setAlignment(MaybeAlign(4));
    GlobalNamedValues[VarName] = globalVar;

    return globalVar;
  } else {
    if (NamedValues.back().find(VarName) != NamedValues.back().end()) {
      error("Local variable " + VarName + " has an existing definition", Tok.lineNo,
            Tok.columnNo);
    }

    AllocaInst *alloca = CreateEntryBlockAlloca(
        Builder.GetInsertBlock()->getParent(), VarName, type);
    NamedValues.back()[VarName] = alloca;

    return alloca;
  }
}

Value *VarReferenceASTNode::codegen() {
  if (AllocaInst *allocaInst = findVar(VarName)) {
    return allocaInst;
  } else if (GlobalNamedValues.find(VarName) != GlobalNamedValues.end()) {
    return GlobalNamedValues[VarName];
  } else {
    error("Undefined variable " + VarName + " referenced", Tok.lineNo, Tok.columnNo);
  }
}

Function *PrototypeASTNode::codegen() {
  vector<Type *> argTypes(Params.size());
  for (unsigned i = 0; i < Params.size(); i++) {
    argTypes[i] = getLLVMType(Params[i]->getVarType());
  }
  FunctionType *funcType =
      FunctionType::get(getLLVMType(FuncType), argTypes, false);
  Function *func = Function::Create(funcType, Function::ExternalLinkage,
                                    FuncName, TheModule.get());

  // Set names for all arguments
  unsigned idx = 0;
  for (Argument &arg : func->args()) {
    arg.setName(Params[idx++]->getVarName());
  }

  return func;
}

Function *FunctionASTNode::codegen() {
  Function *TheFunction = TheModule->getFunction(Proto->getProtoName());

  if (!TheFunction) {
    TheFunction = Proto->codegen();
  } else {
    error("Function " + Proto->getProtoName() + " has an existing definition", Proto->getProtoTok().lineNo,
          Proto->getProtoTok().columnNo);
  }
  BasicBlock *BB = BasicBlock::Create(TheContext, "func", TheFunction);
  Builder.SetInsertPoint(BB);

  // Create a new scope for the function
  NamedValues.clear();
  NamedValues.push_back(map<string, AllocaInst *>());

  // Record the function in the NamedValues map.
  for (Argument &arg : TheFunction->args()) {
    AllocaInst *alloca = CreateEntryBlockAlloca(
        TheFunction, arg.getName().data(), arg.getType());
    Builder.CreateStore(&arg, alloca);
    NamedValues.back()[arg.getName().data()] = alloca;
  }

  // Generate function body
  Value *retVal = Body->codegen();
  for (BasicBlock &BB : *TheFunction) {
    if (BB.getTerminator() != nullptr) {
      continue;
    }
    if (TheFunction->getReturnType()->isVoidTy()) {
      Builder.SetInsertPoint(&BB);
      Builder.CreateRetVoid();
    } else {
      TheModule->print(errs(), nullptr);
      error("Missing return statement in non-void function " + Proto->getProtoName(),
            Proto->getProtoTok().lineNo, Proto->getProtoTok().columnNo);
    }
  }
  if (verifyFunction(*TheFunction, &errs())) {
    error("Function verification failed", Proto->getProtoTok().lineNo,
          Proto->getProtoTok().columnNo);
  }

  return TheFunction;
}

Value *CallASTNode::codegen() {
  Function *calleeFunc = TheModule->getFunction(FuncName);
  if (!calleeFunc) {
    error("Call to undefined function " + FuncName, Tok.lineNo, Tok.columnNo);
  }
  if (calleeFunc->arg_size() != Args.size()) {
    error("Incorrect number of arguments passed to function " + FuncName,
          Tok.lineNo, Tok.columnNo);
  }
  vector<Value *> argsV;
  for (unique_ptr<ASTNode> &arg : Args) {
    Value *argV = arg->codegen();
    argV = loadIfVar(argV);
    if (argV->getType() != calleeFunc->arg_begin()->getType()) {
      argV = cast(argV, calleeFunc->arg_begin()->getType());
      if (!argV) {
        error("Incorrect argument type passed to function " + FuncName,
              Tok.lineNo, Tok.columnNo);
      }
    }
    argsV.push_back(argV);
  }

  return Builder.CreateCall(calleeFunc, argsV, "calltmp");
}

Value *UnaryASTNode::codegen() {
  Value *operand = Operand->codegen();
  operand = loadIfVar(operand);

  if (Op == MINUS) {
    if (operand->getType()->isFloatTy()) {
      return Builder.CreateFNeg(operand, "fnegtmp");
    } else {
      // Cast boolean to integer for integer negation
      return Builder.CreateNeg(castToInt(operand), "negtmp");
    }
  } else {
    // Cast integers and floats for boolean negation
    return Builder.CreateNot(castToBool(operand), "nottmp");
  }
}

Value *BinaryASTNode::codegen() {
  Value *lhs = LHS->codegen();
  Value *rhs = RHS->codegen();

  if (Op != ASSIGN) {
    lhs = loadIfVar(lhs);
  }
  rhs = loadIfVar(rhs);

  if (Op == ASSIGN) {
    if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(lhs)) {
      // Cast right-hand side to the type of the left-hand side
      rhs = cast(rhs, allocaInst->getAllocatedType());
      Builder.CreateStore(rhs, allocaInst);

      return rhs;
    } else if (GlobalVariable *globalVar = dyn_cast<GlobalVariable>(lhs)) {
      // Cast right-hand side to the type of the left-hand side
      rhs = cast(rhs, globalVar->getValueType());
      Builder.CreateStore(rhs, globalVar);

      return rhs;
    } else {
      error("Invalid assignment target", Tok.lineNo, Tok.columnNo);
    }
  }

  if (Op == AND) {
    if (lhs->getType()->isIntegerTy(1) && rhs->getType()->isIntegerTy(1)) {
      return Builder.CreateAnd(lhs, rhs, "andtmp");
    } else {
      if (!lhs->getType()->isIntegerTy(1)) {
        lhs = castToBool(lhs);
      }
      if (!rhs->getType()->isIntegerTy(1)) {
        rhs = castToBool(rhs);
      }

      return Builder.CreateAnd(lhs, rhs, "andtmp");
    }
  } else if (Op == OR) {
    if (lhs->getType()->isIntegerTy(1) && rhs->getType()->isIntegerTy(1)) {
      return Builder.CreateOr(lhs, rhs, "ortmp");
    } else {
      if (!lhs->getType()->isIntegerTy(1)) {
        lhs = castToBool(lhs);
      }
      if (!rhs->getType()->isIntegerTy(1)) {
        rhs = castToBool(rhs);
      }

      return Builder.CreateOr(lhs, rhs, "ortmp");
    }
  }

  // Widen types of left and right hand side if necessary
  Type *exprType = priorityType(lhs->getType(), rhs->getType());
  if (lhs->getType() != exprType) {
    lhs = cast(lhs, exprType);
  }
  if (rhs->getType() != exprType) {
    rhs = cast(rhs, exprType);
  }

  if (Op == PLUS) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFAdd(lhs, rhs, "faddtmp");
    } else {
      return Builder.CreateAdd(lhs, rhs, "addtmp");
    }
  } else if (Op == MINUS) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFSub(lhs, rhs, "fsubtmp");
    } else {
      return Builder.CreateSub(lhs, rhs, "subtmp");
    }
  } else if (Op == ASTERIX) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFMul(lhs, rhs, "fmultmp");
    } else {
      return Builder.CreateMul(lhs, rhs, "multmp");
    }
  } else if (Op == DIV) {
    if (rhs == ConstantInt::get(TheContext, APInt(32, 0, true)) ||
        rhs == ConstantInt::get(TheContext, APInt(1, 0, false)) ||
        rhs == ConstantFP::get(TheContext, APFloat(0.0))) {
      error("Division by zero", Tok.lineNo, Tok.columnNo);
    }
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFDiv(lhs, rhs, "fdivtmp");
    } else {
      return Builder.CreateSDiv(lhs, rhs, "divtmp");
    }
  } else if (Op == MOD) {
    if (rhs == ConstantInt::get(TheContext, APInt(32, 0, true)) ||
        rhs == ConstantInt::get(TheContext, APInt(1, 0, false)) ||
        rhs == ConstantFP::get(TheContext, APFloat(0.0))) {
      error("Modulo by zero", Tok.lineNo, Tok.columnNo);
    }
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFRem(lhs, rhs, "fremtmp");
    } else {
      return Builder.CreateSRem(lhs, rhs, "modtmp");
    }
  } else if (Op == LE) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFCmpULE(lhs, rhs, "fletmp");
    } else {
      return Builder.CreateICmpSLE(lhs, rhs, "letmp");
    }
  } else if (Op == LT) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFCmpULT(lhs, rhs, "flttmp");
    } else {
      return Builder.CreateICmpSLT(lhs, rhs, "lttmp");
    }
  } else if (Op == GE) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFCmpUGE(lhs, rhs, "fgetmp");
    } else {
      return Builder.CreateICmpSGE(lhs, rhs, "getmp");
    }
  } else if (Op == GT) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFCmpUGT(lhs, rhs, "fgttmp");
    } else {
      return Builder.CreateICmpSGT(lhs, rhs, "gttmp");
    }
  } else if (Op == EQ) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFCmpUEQ(lhs, rhs, "feqtmp");
    } else {
      return Builder.CreateICmpEQ(lhs, rhs, "eqtmp");
    }
  } else if (Op == NE) {
    if (lhs->getType()->isFloatTy() && rhs->getType()->isFloatTy()) {
      return Builder.CreateFCmpUNE(lhs, rhs, "fnetmp");
    } else {
      return Builder.CreateICmpNE(lhs, rhs, "netmp");
    }
  }
}

Value *ReturnASTNode::codegen() {
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  Type *retType = TheFunction->getReturnType();

  if (!retType->isVoidTy()) {
    if (!Expr) {
      error("Expected return value for non-void function",
            Tok.lineNo, Tok.columnNo);
    }
    Value *retVal = Expr->codegen();
    retVal = loadIfVar(retVal);
    retVal = cast(retVal, retType);
    if (!retVal) {
      error("Cannot widen return value to function return type", Tok.lineNo,
            Tok.columnNo);
    }
    return Builder.CreateRet(retVal);
  } else {
    if (Expr) {
      error("Unexpected return value for void function", Tok.lineNo,
            Tok.columnNo);
    }
    return Builder.CreateRetVoid();
  }
}

Value *IfASTNode::codegen() {
  Value *cond = Cond->codegen();
  cond = loadIfVar(cond);
  if (!cond->getType()->isIntegerTy(1)) {
    cond = castToBool(cond);
  }

  cond = Builder.CreateICmpNE(
      cond, ConstantInt::get(TheContext, APInt(1, 0, true)), "ifcond");
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  BasicBlock *thenBB = BasicBlock::Create(TheContext, "then", TheFunction);
  BasicBlock *elseBB = BasicBlock::Create(TheContext, "else");
  BasicBlock *mergeBB = BasicBlock::Create(TheContext, "ifcont");

  if (Else) {
    Builder.CreateCondBr(cond, thenBB, elseBB);
  } else {
    Builder.CreateCondBr(cond, thenBB, mergeBB);
  }

  // Emit then value
  Builder.SetInsertPoint(thenBB);
  Then->codegen();
  // If the then block does not have a terminator, add a branch to the merge
  if (Builder.GetInsertBlock()->getTerminator() == nullptr) {
    Builder.CreateBr(mergeBB);
  }

  // Emit else value
  if (Else) {
    TheFunction->insert(TheFunction->end(), elseBB);
    Builder.SetInsertPoint(elseBB);
    Else->codegen();
    // If the else block does not have a terminator, add a branch to the merge
    if (Builder.GetInsertBlock()->getTerminator() == nullptr) {
      Builder.CreateBr(mergeBB);
    }
  }

  // Emit merge block has predecessor from then and else blocks, emit it
  if (!mergeBB->hasNPredecessors(0)) {
    TheFunction->insert(TheFunction->end(), mergeBB);
    Builder.SetInsertPoint(mergeBB);
  }

  return Constant::getNullValue(Type::getInt32Ty(TheContext));
}

Value *WhileASTNode::codegen() {
  Function *TheFunction = Builder.GetInsertBlock()->getParent();
  BasicBlock *condBB = BasicBlock::Create(TheContext, "cond", TheFunction);
  BasicBlock *loopBB = BasicBlock::Create(TheContext, "loop", TheFunction);
  BasicBlock *afterBB = BasicBlock::Create(TheContext, "afterloop");

  // Emit condition block
  Builder.CreateBr(condBB);
  Builder.SetInsertPoint(condBB);
  Value *cond = Cond->codegen();
  cond = loadIfVar(cond);
  // If the condition is not a boolean, cast it to a boolean 
  if (!cond->getType()->isIntegerTy(1)) {
    cond = castToBool(cond);
  }
  cond = Builder.CreateICmpNE(
    cond, ConstantInt::get(TheContext, APInt(1, 0, true)), "whilecond");
  Builder.CreateCondBr(cond, loopBB, afterBB);

  // Emit loop block
  TheFunction->insert(TheFunction->end(), loopBB);
  Builder.SetInsertPoint(loopBB);
  Stmt->codegen();
  // If the loop block does not have a terminator, add a branch to the condition
  if (Builder.GetInsertBlock()->getTerminator() == nullptr) {
    Builder.CreateBr(condBB);
  }

  // Emit after block
  TheFunction->insert(TheFunction->end(), afterBB);
  Builder.SetInsertPoint(afterBB);
  
  return Constant::getNullValue(Type::getInt32Ty(TheContext));
}

Value *BlockASTNode::codegen() {
  // Create a new scope for the block
  NamedValues.push_back(map<string, AllocaInst *>());

  for (unique_ptr<VarASTNode> &var : LocalDecls) {
    var->codegen();
  }
  for (unique_ptr<ASTNode> &stmt : StmtList) {
    stmt->codegen();
    if(Builder.GetInsertBlock()->getTerminator() != nullptr) {
      break;
    }
  }
  // Clean up scope
  NamedValues.pop_back();

  return Constant::getNullValue(Type::getInt32Ty(TheContext));
}

Value *ProgramASTNode::codegen() {
  for (unique_ptr<PrototypeASTNode> &proto : Externs) {
    proto->codegen();
  }
  for (unique_ptr<ASTNode> &decl : Decls) {
    decl->codegen();
  }

  return Constant::getNullValue(Type::getInt32Ty(TheContext));
}

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ASTNode &ast) {
  os << ast.to_string();
  return os;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "Usage: ./code InputFile\n");
    return 1;
  }

  pFile = fopen(argv[1], "r");
  if (pFile == NULL) {
    perror("Error opening file");
    return 1;
  }

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;

  // get the first token
  // getNextToken();
  // while (CurTok.type != EOF_TOK) {
  //  fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
  //          CurTok.type);
  //  getNextToken();
  //}
  // fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = make_unique<Module>("mini-c", TheContext);

  // Run the parser now.
  unique_ptr<ProgramASTNode> program = parser();
  fprintf(stderr, "Parsing Finished\n");
  llvm::outs() << *program << "\n";
  program->codegen();

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  // TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
