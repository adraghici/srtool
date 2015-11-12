package visitor;

import ast.AssertStmt;
import ast.AssignStmt;
import ast.AssumeStmt;
import ast.AtomExpr;
import ast.BinaryExpr;
import ast.BlockStmt;
import ast.CandidateInvariant;
import ast.CandidatePostcondition;
import ast.CandidatePrecondition;
import ast.Expr;
import ast.HavocStmt;
import ast.IfStmt;
import ast.Invariant;
import ast.LoopInvariant;
import ast.Node;
import ast.NumberExpr;
import ast.OldExpr;
import ast.ParenExpr;
import ast.Postcondition;
import ast.PrePostCondition;
import ast.Precondition;
import ast.ProcedureDecl;
import ast.Program;
import ast.ResultExpr;
import ast.Stmt;
import ast.TernaryExpr;
import ast.UnaryExpr;
import ast.VarDeclStmt;
import ast.VarRef;
import ast.VarRefExpr;
import ast.WhileStmt;

public interface Visitor {

    default Object visit(Program program) {
        return visitChildren(program);
    }

    default Object visit(VarDeclStmt varDeclStmt) {
        return visitChildren(varDeclStmt);
    }

    default Object visit(ProcedureDecl procedureDecl) {
        return visitChildren(procedureDecl);
    }

    default Object visit(PrePostCondition prePostCondition) {
        if (prePostCondition instanceof Precondition) {
            return visit((Precondition) prePostCondition);
        } else if (prePostCondition instanceof Postcondition) {
            return visit((Postcondition) prePostCondition);
        } else if (prePostCondition instanceof CandidatePrecondition) {
            return visit((CandidatePrecondition) prePostCondition);
        } else {
            return visit((CandidatePostcondition) prePostCondition);
        }
    }

    default Object visit(Precondition precondition) {
        return visitChildren(precondition);
    }

    default Object visit(Postcondition postcondition) {
        return visitChildren(postcondition);
    }

    default Object visit(CandidatePrecondition candidatePrecondition) {
        return visitChildren(candidatePrecondition);
    }

    default Object visit(CandidatePostcondition candidatePostcondition) {
        return visitChildren(candidatePostcondition);
    }

    default Object visit(AssignStmt assignStmt) {
        return visitChildren(assignStmt);
    }

    default Object visit(AssertStmt assertStmt) {
        return visitChildren(assertStmt);
    }

    default Object visit(AssumeStmt assumeStmt) {
        return visitChildren(assumeStmt);
    }

    default Object visit(HavocStmt havocStmt) {
        return visitChildren(havocStmt);
    }

    default Object visit(IfStmt ifStmt) {
        return visitChildren(ifStmt);
    }

    default Object visit(WhileStmt whileStmt) {
        return visitChildren(whileStmt);
    }

    default Object visit(BlockStmt blockStmt) {
        return visitChildren(blockStmt);
    }

    default Object visit(LoopInvariant loopInvariant) {
        if (loopInvariant instanceof Invariant) {
            return visit((Invariant) loopInvariant);
        } else {
            return visit((CandidateInvariant) loopInvariant);
        }
    }

    default Object visit(Invariant invariant) {
        return visitChildren(invariant);
    }

    default Object visit(CandidateInvariant candidateInvariant) {
        return visitChildren(candidateInvariant);
    }

    default Object visit(VarRef varRef) {
        return visitChildren(varRef);
    }

    default Object visit(Expr expr) {
        if (expr instanceof TernaryExpr) {
            return visit((TernaryExpr) expr);
        } else if (expr instanceof BinaryExpr) {
            return visit((BinaryExpr) expr);
        } else if (expr instanceof UnaryExpr) {
            return visit((UnaryExpr) expr);
        } else {
            return visit((AtomExpr) expr);
        }
    }

    default Object visit(Stmt stmt) {
        if (stmt instanceof VarDeclStmt) {
            return visit((VarDeclStmt) stmt);
        } else if (stmt instanceof AssignStmt) {
            return visit((AssignStmt) stmt);
        } else if (stmt instanceof AssertStmt) {
            return visit((AssertStmt) stmt);
        } else if (stmt instanceof AssumeStmt) {
            return visit((AssumeStmt) stmt);
        } else if (stmt instanceof HavocStmt) {
            return visit((HavocStmt) stmt);
        } else if (stmt instanceof IfStmt) {
            return visit((IfStmt) stmt);
        } else if (stmt instanceof WhileStmt) {
            return visit((WhileStmt) stmt);
        } else {
            return visit((BlockStmt) stmt);
        }
    }

    default Object visit(TernaryExpr ternaryExpr) {
        return visitChildren(ternaryExpr);
    }

    default Object visit(BinaryExpr binaryExpr) {
        return visitChildren(binaryExpr);
    }

    default Object visit(UnaryExpr unaryExpr) {
        return visitChildren(unaryExpr);
    }

    default Object visit(AtomExpr atomExpr) {
        if (atomExpr instanceof NumberExpr) {
            return visit((NumberExpr) atomExpr);
        } else if (atomExpr instanceof VarRefExpr) {
            return visit((VarRefExpr) atomExpr);
        } else if (atomExpr instanceof ParenExpr) {
            return visit((ParenExpr) atomExpr);
        } else if (atomExpr instanceof ResultExpr) {
            return visit((ResultExpr) atomExpr);
        } else {
            return visit((OldExpr) atomExpr);
        }
    }

    default Object visit(NumberExpr numberExpr) {
        return visitChildren(numberExpr);
    }

    default Object visit(VarRefExpr varRefExpr) {
        return visitChildren(varRefExpr);
    }

    default Object visit(ParenExpr parenExpr) {
        return visitChildren(parenExpr);
    }

    default Object visit(ResultExpr resultExpr) {
        return visitChildren(resultExpr);
    }

    default Object visit(OldExpr oldExpr) {
        return visitChildren(oldExpr);
    }

    default Object visit(Node node) {
        return null;
    }

    default Object visitChildren(Node node) {
        node.getChildren().forEach(this::visit);
        return node;
    }
}
