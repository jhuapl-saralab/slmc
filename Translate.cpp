/*
 * Copyright (c) 2016, Johns Hopkins University Applied Physics Laboratory
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <cstdio>
#include <memory>
#include <string>
#include <sstream>
#include <iostream>
#include <fstream>
#include <iterator>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/ParseAST.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
	public:
		MyASTVisitor(SourceManager &SM) : TheSourceManager(SM) {}
		bool VisitRecordDecl(RecordDecl * crd) {
			std::string recordName = crd->getNameAsString();
			std::stringstream fields;
			if (existsRecordFile) {
				recordFile.open("records.v", std::ofstream::out | std::ofstream::app);
			} else {
				recordFile.open("records.v");
				existsRecordFile = true;
			}
			if (!recordFile.is_open()) {
				std::cout << "Cannot create records file\n";
				existsRecordFile = false;
				return false;
			}
			RecordDecl::field_iterator itr;
			for (itr = crd->field_begin(); itr != crd->field_end(); itr++) {
				if (itr == crd->field_begin()) {
					fields << ExploreDecl(*itr);
				} else {
					fields << ";" << ExploreDecl(*itr);
				}
			}
			recordFile << "Record "
				<< recordName
				<< " : Type := "
				<< "mk_" << recordName
				<< "{"
				<< fields.str()
				<< "}.\n";
			recordFile.close();
			return false;
		}
		bool VisitFunctionDecl(FunctionDecl *f) {
			std::string locals_list = "nil";
			std::string var_decl = "";
			std::set<std::string>::iterator itr;
			if (f->hasBody()) {
				std::ofstream coqfile;
				std::string function_name = f->getNameInfo().getName().getAsString();
				std::string filename  = function_name + ".v";
				coqfile.open(filename);
				if (!coqfile.is_open()) {
					std::cout << "Cannot create file " << filename << "\n";
					return false;
				}
				//Clear out any variables from a previous function
				//and insert return' and errno' which are always there
				//even if they aren't used.  As a bonus, there shouldn't be any
				//naming conflicts with these as ' is not allowed in a variable name
				//in C, but is allowed in COQ
				vars.clear();
				vars.insert("return'");
				vars.insert("errno'");
				//Populate the vars set with the parameters of the function
				for(ParmVarDecl ** itr = f->param_begin(); itr != f->param_end(); itr++) {
					ExploreDecl(*itr);
				}
				//The parameters are now assumed to be in the locals set
				for(itr = vars.begin(); itr != vars.end(); itr++) {
					locals_list = *itr + "::" + locals_list;
				}
				//Convert the function body to sl-mech "code", and as a side effect
				//pick up all declared variables
				Stmt * FuncBody = cast<Stmt>(f->getBody());
				std::string program = ExploreStmt(FuncBody);
				//List out the declared variables (x y z : var) for the precondition
				if (!vars.empty()) {
					var_decl = ": var)";
					for (itr = vars.begin(); itr != vars.end(); itr++) {
						var_decl = *itr + " " + var_decl;
					}
					var_decl = "(" + var_decl;
				}
				//Create the main body of our theorem
				coqfile << "Theorem "
					<< function_name
					<<" :\n"  //The theorem has the same name as our function
					<< "forall" //Some preconditions that are always true
					<< " (st2 : state) "
					<< "(s : store_f)(h : heap_f)(l : locals)(d : domain)"
					<< var_decl // the declared variables from earlier
					<< ","
					<< "(lift_prop_sprop (store_bits "
					<< locals_list //special + paraemeter vars are local
					<< " l) )"
					<< "(*ADDITIONAL_PRECONDITIONS*)" //User defined preconditions?
					<< "{|srf := s ; lc := l ; hpf := h ; dm := d|}"//Start state
					<< "\n->\n(completes {|srf := s ; lc := l ; hpf := h ; dm := d|} st2\n"
					<< program //The main body of the function
					<< ")->(*POSTCONDITIONS*) st2\n\n"; //User defined postconditions
				coqfile.close();
			}
			//We don't want the walker to go through the rest of this as we take care of it ourselves
			return false;
		}

	private:
		std::set<std::string> vars; //The set of all variables in a function
		std::ofstream recordFile;
		bool existsRecordFile = false;
		SourceManager &TheSourceManager;
		//Attempts to translate a unary operator into the proper sl-mech code
		std::string ExploreUnOp(UnaryOperator * uo) {
			bool hasAssignment = false;  //is the unary operator assigning a value to a variable
			std::string sl_op;  //the corresponding binary sl-mech operator
			std::stringstream lhs;  //The left hand side of the sl-mech operator
			std::stringstream rhs;  //The right hand side of the sl-mech operator
			Expr * subExpr = uo->getSubExpr();  //The subexpression of the unary operator
			std::string sub_str = ExploreExpr(subExpr); //Recursively walks down this branch 
			std::stringstream ss;  //For expressions that do not fit the "usual" mold
			switch (uo->getOpcode()) {
				case UO_PostInc :
					hasAssignment = true;
					sl_op = "eplus";
					rhs << " ( "
						<< typeModifier(subExpr)
						<< " 1 ) ";
					lhs << sub_str;
					break;
				case UO_PostDec :
					hasAssignment = true;
					sl_op = "eminus";
					rhs << " ( "
						<< typeModifier(subExpr)
						<< " 1 ) ";
					lhs << sub_str;
					break;
				case UO_PreInc :  //These don't capture the order of the assignments properly
					hasAssignment = true;
					sl_op = "eplus";
					rhs << " ( "
						<< typeModifier(subExpr)
						<< " 1 ) ";
					lhs << sub_str;
					break;
				case UO_PreDec :
					hasAssignment = true;
					sl_op = "eplus";
					rhs << " ( "
						<< typeModifier(subExpr)
						<< " 1 ) ";
					lhs << sub_str;
					break;
				case UO_AddrOf :
					ss << "["
						<< sub_str
						<< "]";
					return ss.str();
				case UO_Deref :
					ss << "["
						<< sub_str
						<< "]";
					return ss.str();
				case UO_Plus :
					hasAssignment = false;
					sl_op = "eplus";
					lhs << " ( "
						<< typeModifier(subExpr)
						<< " 0 ) ";
					rhs << sub_str;
					break;
				case UO_Minus :
					hasAssignment = false;
					sl_op = "eminus";
					lhs << " ( "
						<< typeModifier(subExpr)
						<< " 0 ) ";
					rhs << sub_str;
					break;
				case UO_Not :
					return "BITWISE_NOT_PLACEHOLDER";
				case UO_LNot :
					ss << " ( bnot ( "
						<< sub_str
						<< " ) ) ";
					return ss.str();
				case UO_Real :
					return "REAL_PLACEHOLDER";
				case UO_Imag :
					return "IMAG_PLACEHOLDER";
				case UO_Extension :
					return "EXTENSION_PLACEHOLDER";
				default :
					return "UNKNOWN_UNARY_OP";
			}
			return createBinOp(lhs.str(), rhs.str(), sl_op, hasAssignment);
		}
		//Produces sl-mech code for binary operators
		std::string ExploreBinOp(BinaryOperator * bo) {
			std::string lhs_str = ExploreExpr(bo->getLHS());//Recursively explore the left
			std::string rhs_str = ExploreExpr(bo->getRHS());//and right hand sides of the binop
			std::string sl_op;//This is the sl-mech operator
			bool hasAssignment;//This tells us if the binary operator does an assignment
			std::stringstream ss;//For unusual binary operators
			switch (bo->getOpcode()) {
				case BO_PtrMemD :
					return "PTR_MEMD_PLACEHOLDER";
				case BO_PtrMemI :
					return "PTR_MEMI_PLACEHODLER";
				case BO_Mul :
					sl_op = "emul";
					hasAssignment = false;
					break;
				case BO_Div :
					sl_op = "ediv";
					hasAssignment = false;
					break;
				case BO_Rem :
					sl_op = "emod";
					hasAssignment = false;
					break;
				case BO_Add :
					sl_op = "eplus";
					hasAssignment = false;
					break;
				case BO_Sub :
					sl_op = "eminus";
					hasAssignment = false;
					break;
				case BO_Shl :
					return "SHL_PLACEHOLDER";
				case BO_Shr :
					return "SHR_PLACEHOLDER";
				case BO_LT :
					sl_op = "blt";
					hasAssignment = false;
					break;
				case BO_GT :
					sl_op = "bgt";
					hasAssignment = false;
					break;
				case BO_LE :
					sl_op = "ble";
					hasAssignment = false;
					break;
				case BO_GE :
					sl_op = "bge";
					hasAssignment = false;
					break;
				case BO_EQ :
					sl_op = "beq";
					hasAssignment = false;
					break;
				case BO_NE :
					ss << "bnot("
						<< createBinOp(lhs_str, rhs_str, "beq", false)
						<< ")";
					return ss.str(); 
				case BO_And :
					return "BITWISE_AND_PLACEHOLDER";
				case BO_Xor :
					return "BITWISE_XOR_PLACEHOLDER";
				case BO_Or :
					return "BITWISE_OR_PLACEHOLDER";
				case BO_LAnd :
					sl_op = "band";
					hasAssignment = false;
					break;
				case BO_LOr :
					sl_op = "bor";
					hasAssignment = false;
					break;
				case BO_Assign :
					ss << lhs_str
						<< "≔"
						<< rhs_str;
					return ss.str(); 
				case BO_MulAssign :
					sl_op = "emul";
					hasAssignment = true;
					break;
				case BO_DivAssign :
					sl_op = "ediv";
					hasAssignment = true;
					break;
				case BO_RemAssign :
					sl_op = "emod";
					hasAssignment = true;
					break;
				case BO_AddAssign :
					sl_op = "eplus";
					hasAssignment = true;
					break;
				case BO_SubAssign :
					sl_op = "eminus";
					hasAssignment = true;
					break;
				case BO_ShlAssign :
					return "SHL_ASSIGN_PLACEHOLDER";
				case BO_ShrAssign :
					return "SHR_ASSIGN_PLACEHOLDER";
				case BO_AndAssign :
					return "BITWISE_AND_ASSIGN_PLACEHOLDER";
				case BO_XorAssign :
					return "BITWISE_XOR_ASSIGN_PLACEHOLDER";
				case BO_OrAssign :
					return "BITWISE_OR_ASSIGN_PLACEHOLDER";
				case BO_Comma :
					return "COMMA_PLACEHOLDER";
				default :
					return "UNKNOWN BINOP\n";
			}
			return createBinOp(lhs_str, rhs_str, sl_op, hasAssignment);
		}

		//Given an expression this determines the type of expression and builds the proper
		//sl-mech code from there
		std::string ExploreExpr(Expr * e) {
			if (e == NULL) {
				return "EMPTY_EXPR";
			}
			std::stringstream ss;
			//Reference to an already declared variable
			//so far we only need the name
			if (isa<DeclRefExpr>(e)) {
				DeclRefExpr * dre = cast<DeclRefExpr>(e);
				ss << dre->getNameInfo().getAsString();
				return ss.str();
			}
			//An integer of any type
			if (isa<IntegerLiteral>(e)) {
				IntegerLiteral * il = cast<IntegerLiteral>(e);
				//Extract the variable type and value
				ss << " ( "
					<< typeModifier(e) 
					<< " "
					<< il->getValue().getLimitedValue()
					<< " ) ";
				return ss.str();
			}
			//A binary operator
			if (isa<BinaryOperator>(e)) {
				BinaryOperator * bo = cast<BinaryOperator>(e);
				return ExploreBinOp(bo);
			}
			//We don't really care about the implicit cast here,
			//just the expression contained within
			if (isa<ImplicitCastExpr>(e)) {
				ImplicitCastExpr * ice = cast<ImplicitCastExpr>(e);
				return ExploreExpr(ice->getSubExpr());
			}
			//Unary operator
			if (isa<UnaryOperator>(e)) {
				UnaryOperator * uo = cast<UnaryOperator>(e);
				return ExploreUnOp(uo); 
			}
			e->dumpColor();
			ss << "UNKNOWN EXPR\n";
			return ss.str();

		}
		//Given a declaration this determines the type of declaration and builds the proper sl-mech code
		std::string ExploreDecl(Decl * d) {
			std::stringstream ss;
			//An empty declaration
			if (isa<EmptyDecl>(d)) {
				return "skip";
			}
			//A variable declaration
			if (isa<VarDecl>(d)) {
				VarDecl * nd = cast<VarDecl>(d);
				std::string varName = nd->getNameAsString();
				vars.insert(varName); //Add the name to the set of all vars
				ss << "local "
					<< varName  //locals x skip
					<< " skip";
				if (nd->hasInit() && nd->getInitStyle() == VarDecl::CInit) {
					//This is a decl that also initializes the var
					ss << ";; ( assign "
						<< varName
						<< " "
						<< ExploreExpr(nd->getInit())
						<< " ) "; //local x skip;;assign x y
				}
				return ss.str();
			}
			if (isa<FieldDecl>(d)) {
				FieldDecl * fd = cast<FieldDecl>(d);
				ss << fd->getNameAsString() << " : var ";
				return ss.str();
			}
			if (isa<RecordDecl>(d)) {
				RecordDecl * crd = cast<RecordDecl>(d);
				std::string recordName = crd->getNameAsString();
				std::stringstream fields;
				RecordDecl::field_iterator itr;
				for (itr = crd->field_begin(); itr != crd->field_end(); itr++) {
					fields << ExploreDecl(*itr);
				}
				ss << "Record "
					<< recordName
					<< " : Set := "
					<< "mk" << recordName
					<< "{"
				        << fields.str()
					<< "}";
			}
			d->dumpColor();
			return "UNKNOWN DECL\n";

		}
		//Given a statement, determine the type of statement and build the proper sl-mech code
		std::string ExploreStmt(Stmt * s) {
			if (s == NULL)
				return " skip";
			std::stringstream ss;
			//Compound statement as in {stmt;stmt}
			if (isa<CompoundStmt>(s)) {
				CompoundStmt * cs = cast<CompoundStmt>(s);
				//Iterate through the compound statement, translating sequentially
				ss << "(";
				for(Stmt ** itr = cs->body_begin(); itr != cs->body_end(); itr++) {
					ss << ExploreStmt(*itr) << ";;\n";
				}
				ss << "skip)";
				return ss.str();
			}
			//This is a statement about (possibly many) declarations
			if (isa<DeclStmt>(s)) {
				DeclStmt * ds = cast<DeclStmt>(s);
				//Iterate through each declaration, traslating sequentially
				ss << "(";
				for (Decl ** itr = ds->decl_begin(); itr != ds->decl_end(); itr++) {
					ss << ExploreDecl(*itr) << ";;";
				}
				ss << "skip)";
				return ss.str();
			}
			//A do-while loop
			if (isa<DoStmt>(s)) {
				DoStmt * ds = cast<DoStmt>(s);
				std::string body = ExploreStmt(ds->getBody());
				//Only while loops exist in sl-mech, so this translates to
				//do{body}while(cond) -> {body while(cond) {body}}
				ss << body
					<< " ( while "
					<< ExploreExpr(ds->getCond())
					<< body
					<< " ) ";
				return ss.str();
			}
			//A for loop
			if (isa<ForStmt>(s)) {
				ForStmt * fs = cast<ForStmt>(s);
				//Only while loops exist in sl-mech so we translate to
				//for(init;cond;incr){body} -> {init; while(cond){body;incr;}}
				ss << ExploreStmt(fs->getInit())
					<< ";; ( while "
					<< ExploreExpr(fs->getCond())
					<< ExploreStmt(fs->getBody())
					<< ExploreExpr(fs->getInc())
					<< " ) ";
				return ss.str();
			}
			//An if statement
			if (isa<IfStmt>(s)) {
				IfStmt * is = cast<IfStmt>(s);
				ss << " (ifelse "
					<< ExploreExpr(is->getCond())
					<< ExploreStmt(is->getThen())
					<< ExploreStmt(is->getElse()) 
					<< " ) ";
				return ss.str();
			}
			//The empty statemnt ";"
			if (isa<NullStmt>(s)) {
				ss << "skip";
				return ss.str();
			}
			//The return statement in a function
			if (isa<ReturnStmt>(s)) {
				ReturnStmt * rs = cast<ReturnStmt>(s);
				ss << " ( assign __return__ " //Not quite right for void function returns
					<< ExploreExpr(rs->getRetValue())
					<< " ) ;; ret ";
				return ss.str();
			}
			//A while statement
			if (isa<WhileStmt>(s)){
				WhileStmt * ws = cast<WhileStmt>(s);
				ss << " ( while "
					<< ExploreExpr(ws->getCond())
					<< ExploreStmt(ws->getBody())
					<< " ) ";
				return ss.str();
			}
			//An expression
			if (isa<Expr>(s)) {
				Expr * e = cast<Expr>(s);
				return ExploreExpr(e);
			}
			s->dumpColor();
			ss << "UNKNOWN STMT TYPE\n";
			return ss.str();
		}
		//Constructs a binary operation from the left hand side, right hand side, and
		//the name of the operator in sl-mech
		std::string createBinOp(std::string lhs, std::string rhs,
				std::string binOp, bool isAssignment) {
			std::stringstream ss;
			if (!isAssignment) {
				ss << binOp
					<< " ("
					<< lhs
					<< " "
					<< rhs
					<< ") ";
			} else {
				//This is for operators such as += and *=
				ss << " ( assign "
					<< lhs
					<< " "
					<< createBinOp(lhs, rhs, binOp, false)
					<< " ) ";
			}
			return ss.str();
		}
		//Given an integer and a C type, this casts the integer into a val in sl-mech
		std::string typeModifier(Expr * e) {
			std::string type_str;
			const Type * ty = e->getType().getTypePtr();
			if (ty->isBuiltinType()) {
				const BuiltinType * bt = dyn_cast<BuiltinType>(ty);
				switch (bt->getKind()) {
					case BuiltinType::Int :
						type_str = "Z_to_sint32 "; break;
					case BuiltinType::UInt :
						type_str = "Z_to_uint32 "; break;
					case BuiltinType::Long :
						type_str = "Z_to_sint64 "; break;
					case BuiltinType::ULong :
						type_str = "Z_to_uint64 "; break;
					default :
						type_str = "TYPE_NOT_HANDLED "; break;
				}
			} else {
				type_str = "NON_CANONICAL_TYPE ";
			}
			return type_str;
		}

};

class MyASTConsumer : public ASTConsumer {
	public:
		MyASTConsumer(SourceManager &SM) : Visitor(SM) {}

		virtual bool HandleTopLevelDecl(DeclGroupRef DR) {
			for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b)
				Visitor.TraverseDecl(*b);
			return true;
		}

	private:
		MyASTVisitor Visitor;
};

int main(int argc, char *argv[]) {
	if (argc < 2) {
		llvm::errs() << "Usage: " << argv[0] << " <filename>\n";
		return 1;
	}

	CompilerInstance TheCompInst;
	TheCompInst.createDiagnostics();

	LangOptions &lo = TheCompInst.getLangOpts();
	lo.CPlusPlus = 1;

	auto TO = std::make_shared<TargetOptions>();
	TO->Triple = llvm::sys::getDefaultTargetTriple();
	TargetInfo *TI =
		TargetInfo::CreateTargetInfo(TheCompInst.getDiagnostics(), TO);
	TheCompInst.setTarget(TI);

	TheCompInst.createFileManager();
	FileManager &FileMgr = TheCompInst.getFileManager();
	TheCompInst.createSourceManager(FileMgr);
	SourceManager &SourceMgr = TheCompInst.getSourceManager();
	TheCompInst.createPreprocessor(TU_Module);
	TheCompInst.createASTContext();

	const FileEntry *FileIn = FileMgr.getFile(argv[1]);
	SourceMgr.setMainFileID(
			SourceMgr.createFileID(FileIn, SourceLocation(), SrcMgr::C_User));
	TheCompInst.getDiagnosticClient().BeginSourceFile(
			TheCompInst.getLangOpts(), &TheCompInst.getPreprocessor());

	MyASTConsumer TheConsumer(SourceMgr);

	ParseAST(TheCompInst.getPreprocessor(), &TheConsumer,
			TheCompInst.getASTContext());

	return 0;
}
