package visitor;

import ast.*;

public class ASTPrintVisitor implements ASTVisitor {

    @Override
    public String visit(AssertStmt assertStmt) {
        return "";
    }

    @Override
    public String visit(AssignStmt assignStmt) {
        return "";
    }

    @Override
    public String visit(AssumeStmt assumeStmt) {
        return "";
    }

    @Override
    public String visit(BinaryExpr binaryExpr) {
        return "";
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        return "";
    }

    @Override
    public String visit(CandidatePostcondition candidatePostcondition) {
        return "";
    }

    @Override
    public String visit(CandidatePrecondition candidatePrecondition) {
        return "";
    }

    @Override
    public String visit(HavocStmt havocStmt) {
        return "";
    }

    @Override
    public String visit(IfStmt ifStmt) {
        return "";
    }

    @Override
    public String visit(NumberExpr numberExpr) {
        return "";
    }

    @Override
    public String visit(Node node) {
        return "";
    }

    @Override
    public String visit(OldExpr oldExpr) {
        return "";
    }

    @Override
    public String visit(ParenExpr parenExpr) {
        return "";
    }

    @Override
    public String visit(Postcondition postcondition) {
        return "";
    }

    @Override
    public String visit(Precondition precondition) {
        return "";
    }

    @Override
    public String visit(ProcedureDecl procedureDecl) {
        return "";
    }

    @Override
    public String visit(Program program) {
        StringBuilder result = new StringBuilder();

        for (VarDeclStmt varDeclStmt : program.getGlobalDecls()) {
            result.append(visit(varDeclStmt));
        }

        for (ProcedureDecl procedureDecl : program.getProcedureDecls()) {
            result.append(visit(procedureDecl));
        }

        return result.toString();
    }

    @Override
    public String visit(ResultExpr resultExpr) {
        return "";
    }

    @Override
    public String visit(TernaryExpr ternaryExpr) {
        return "";
    }

    @Override
    public String visit(UnaryExpr unaryExpr) {
        return "";
    }

    @Override
    public String visit(VarDeclStmt varDeclStmt) {
        return "int " + varDeclStmt.getVar() + ";\n";
    }

    @Override
    public String visit(VarRefExpr varRefExpr) {
        return "";
    }
}
