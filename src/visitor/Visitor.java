package visitor;

import ast.AssertStmt;
import ast.AssignStmt;
import ast.AssumeStmt;
import ast.BinaryExpr;
import ast.BlockStmt;
import ast.CallStmt;
import ast.CandidateInvariant;
import ast.CandidatePostcondition;
import ast.CandidatePrecondition;
import ast.HavocStmt;
import ast.IfStmt;
import ast.Invariant;
import ast.NumberExpr;
import ast.OldExpr;
import ast.ParenExpr;
import ast.Postcondition;
import ast.Precondition;
import ast.ProcedureDecl;
import ast.ProcedureRef;
import ast.Program;
import ast.ResultExpr;
import ast.TernaryExpr;
import ast.UnaryExpr;
import ast.VarDeclStmt;
import ast.VarRef;
import ast.VarRefExpr;
import ast.WhileStmt;

public interface Visitor<T> {

    T visit(Program program);

    T visit(VarDeclStmt varDeclStmt);

    T visit(ProcedureDecl procedureDecl);

    T visit(Precondition precondition);

    T visit(Postcondition postcondition);

    T visit(CandidatePrecondition candidatePrecondition);

    T visit(CandidatePostcondition candidatePostcondition);

    T visit(AssignStmt assignStmt);

    T visit(AssertStmt assertStmt);

    T visit(AssumeStmt assumeStmt);

    T visit(HavocStmt havocStmt);

    T visit(CallStmt callStmt);

    T visit(IfStmt ifStmt);

    T visit(WhileStmt whileStmt);

    T visit(BlockStmt blockStmt);

    T visit(Invariant invariant);

    T visit(CandidateInvariant candidateInvariant);

    T visit(VarRef varRef);

    T visit(TernaryExpr ternaryExpr);

    T visit(BinaryExpr binaryExpr);

    T visit(UnaryExpr unaryExpr);

    T visit(NumberExpr numberExpr);

    T visit(VarRefExpr varRefExpr);

    T visit(ParenExpr parenExpr);

    T visit(ResultExpr resultExpr);

    T visit(OldExpr oldExpr);

    T visit(ProcedureRef procedureRef);

    String getDescription();
}
