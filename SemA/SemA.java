package SemA;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

public class SemA {
    static int loopDepth = 0;
    static int nodeId = 0;
    static int scopeNodeId = 0;
    static HashSet<String> definedFunctions = new HashSet<>();
    static Stack<Type> functionStack = new Stack<>();
    // nodes used to analyze input
    static class Node {
        int id;
        String label;
        List<Node> children = new ArrayList<>();
        // expression attributes
        Type type;
        Type itype; // inherited type - type of parent
        boolean lvalue;
        List<Type> types = null; // lista tipova argumenata (za <lista_argumenata>)
        List<String> lexValues = null;

        // variables important for output
        int row = -1;
        String lexValue = null;


        public Node() {
            this.id = nodeId++;
        }
    }

    static class scopeNode {
        int id;
        HashSet<Symbol> localVariables = new HashSet<>();
        scopeNode parent;

        public scopeNode(scopeNode parent) {
            this.id = scopeNodeId++;
            this.parent = parent;
        }

    }

    static class Type {
        enum Basic {INT, CHAR, VOID};

        Basic basic;
        boolean isSequence = false;
        boolean isConst = false;
        boolean isFunction = false;
        Type returnType = null;  // povratni tip funkcije (pov)
        List<Type> paramTypes = null;  // tipovi parametara funkcije (params)
        Integer elemNr = null;

        Type(Basic basic) {
            this.basic = basic;
        }
        Type(Type t){
            this.basic = t.basic;
            this.isSequence = t.isSequence;
            this.isConst = t.isConst;
            this.isFunction = t.isFunction;
            this.returnType = t.returnType;
            this.paramTypes = t.paramTypes;
            this.elemNr = t.elemNr;
        }
    }

    static class Symbol {
        String lexValue;

        // expression attributes
        Type type;
        String label;
        Type itype; // inherited type - type of parent
        boolean lvalue;

        Symbol(String name, Type type) {
            this.lexValue = name;
            this.type = type;
        }

        @Override
        public boolean equals(Object other){
            if (other == null) return false;
            if (!(other instanceof Symbol)) return false;

            Symbol o = (Symbol) other;

            return o.hashCode() == this.hashCode();
        }
        @Override
        public int hashCode(){
            return this.type.hashCode() + this.lexValue.hashCode();
        }
    }

    private static int depth(String line){
        int i = 0;
        while (i < line.length() && line.charAt(i) == ' ') i++;
        return i;
    }

    private static Node parseLine(String line){
        line =  line.trim();
        String[] parts = line.split(" ");

        Node node = new Node();
        node.label = parts[0];

        // if row contains terminated
        if (!parts[0].startsWith("<")){
            // epsilon row (empty)
            if (parts[0].equals("$")) return node;

            // row number is the second part of the line
            node.row = Integer.parseInt(parts[1]);

            // lexvalue is the rest of the line
            StringBuilder sb = new StringBuilder();
            for (int i = 2; i < parts.length; i++){
                sb.append(parts[i]);
                if (i < parts.length-1) sb.append(" ");
            }
            node.lexValue = sb.toString();
        }

        return node;
    }

    // parse tree from sintax analysis output
    private static Node loadTree() throws IOException{
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        String line;
        Stack<Node> stack= new Stack<>();
        Node root = null;

        while ((line = br.readLine()) != null) {
            if (line.isEmpty()) continue;

            int d = depth(line);
            Node node = parseLine(line);

            // get to the right level (depth)
            while (stack.size() > d){
                stack.pop();
            }

            if (stack.isEmpty()){
                // node becomes the root
                root = node;
            }else{
                // node becomes a child of the last node on the stack
                stack.peek().children.add(node);
            }
            stack.push(node);

        }

        return root;
    }

    static Stack<scopeNode> scopeStack = new Stack<>();

    private static scopeNode newScope() {
        scopeNode parent = null;
        if (!scopeStack.isEmpty()){
            parent = scopeStack.peek();
        }
        scopeNode ns = new scopeNode(parent);
        scopeStack.push(ns);
        return ns;
    }

    static void ispisiStablo(Node c, int dubina) {
        System.out.print(" ".repeat(dubina));
        System.out.println(c.id +
                (c.lexValue != null ? " (" + c.lexValue + ")" : "")
        );

        for (Node dijete : c.children) {
            ispisiStablo(dijete, dubina + 1);
        }
    }

    static boolean canAssign(Type from, Type to) {
        if (from == null || to == null)
            return false;

        // Nizovi
        if (from.isSequence || to.isSequence) {
            // Oba moraju biti nizovi
            if (!from.isSequence || !to.isSequence)
                return false;

            // Osnovni tipovi moraju biti isti
            if (from.basic != to.basic)
                return false;

            // niz(T) -> niz(T) - refleksivnost
            if (!from.isConst && !to.isConst)
                return true;

            // niz(const(T)) -> niz(const(T)) - refleksivnost
            if (from.isConst && to.isConst)
                return true;

            // niz(T) -> niz(const(T)) - gdje T nije const
            if (!from.isConst && to.isConst)
                return true;

            // niz(const(T)) -> niz(T) - NE
            return false;
        }

        // Primitivni tipovi - isti basic type (const se ignorira za kompatibilnost)
        // T -> T, const(T) -> T, T -> const(T), const(T) -> const(T)
        if (from.basic == to.basic)
            return true;

        // char -> int (bez obzira na const)
        // char -> int, const(char) -> int, char -> const(int), const(char) -> const(int)
        if (from.basic == Type.Basic.CHAR && to.basic == Type.Basic.INT)
            return true;

        return false;
    }

    static boolean canExplicitAssign(Type from, Type to) {
        if(canAssign(from, to))
            return true;
        return from.basic == Type.Basic.INT && to.basic == Type.Basic.CHAR;
    }


    static void process(Node node){
        switch(node.label) {
            case "<primarni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("IDN")) {
                    boolean found = false;
                    scopeNode curr = scopeStack.peek();
                    while (!found && curr != null) {
                        for (Symbol s : curr.localVariables)
                            if (s.label.equals("IDN") && s.lexValue.equals(node.children.get(0).lexValue)) {
                                found = true;

                                node.type = s.type;
                                node.lvalue = s.lvalue;
                            }
                        curr = curr.parent;
                    }

                    if (!found) {
                        err(node);
                    }
                } else if (node.children.size() == 1 && node.children.get(0).label.equals("BROJ")) {
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else if (node.children.size() == 1 && node.children.get(0).label.equals("ZNAK")) {
                    node.type = new Type(Type.Basic.CHAR);
                    node.lvalue = false;
                } else if (node.children.size() == 1 && node.children.get(0).label.equals("NIZ_ZNAKOVA")) {
                    node.type = new Type(Type.Basic.CHAR);
                    node.type.isSequence = true;
                    node.type.isConst = true;
                    node.lvalue = false;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("L_ZAGRADA") && node.children.get(1).label.equals("<izraz>") && node.children.get(2).label.equals("D_ZAGRADA")) {
                    node.type = new Type(node.children.get(1).type);
                    node.lvalue = node.children.get(1).lvalue;
                    process(node.children.get(1));
                }
                break;

            case "<postfiks izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<primarni_izraz>")) {
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                    process(node.children.get(0));
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_UGL_ZAGRADA") && node.children.get(2).label.equals("<izraz>") && node.children.get(3).label.equals("D_UGL_ZAGRADA")) {
                    Node postfiks = node.children.get(0);
                    Node izraz = node.children.get(2);

                    process(postfiks);

                    if (postfiks.type == null || !postfiks.type.isSequence) {
                        // error
                        err(node);
                    }

                    Type elementType = new Type(postfiks.type.basic);
                    elementType.isSequence = false;
                    elementType.isConst = postfiks.type.isConst;
                    node.type = elementType;

                    node.lvalue = !elementType.isConst;

                    process(izraz);

                    Type intType = new Type(Type.Basic.INT);
                    if (izraz.type == null || !canAssign(izraz.type, intType)) {
                        // error
                        err(node);
                    }
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("D_ZAGRADA")) {
                    Node postfiks = node.children.get(0);

                    // 1. provjeri(<postfiks_izraz>)
                    process(postfiks);

                    // 2. <postfiks_izraz>.tip = funkcija(void → pov)
                    if (postfiks.type == null || !postfiks.type.isFunction) {
                        // error
                        err(node);
                    }

                    node.type = new Type(postfiks.type.returnType);
                    node.lvalue = false;
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<lista_argumenata>") && node.children.get(3).label.equals("D_ZAGRADA")) {
                    Node postfiks = node.children.get(0);
                    Node listaArgumenata = node.children.get(2);

                    process(postfiks);

                    process(listaArgumenata);

                    if (postfiks.type == null || !postfiks.type.isFunction) {
                        // error
                        err(node);
                    }

                    // Provjeri da broj argumenata odgovara broju parametara
                    if (postfiks.type.paramTypes == null || listaArgumenata.types == null ||
                            postfiks.type.paramTypes.size() != listaArgumenata.types.size()) {
                        // error: broj argumenata ne odgovara broju parametara
                        err(node);
                    }

                    // Provjeri da su tipovi argumenata kompatibilni s tipovima parametara (redom)
                    for (int i = 0; i < postfiks.type.paramTypes.size(); i++) {
                        Type argType = listaArgumenata.types.get(i);
                        Type paramType = postfiks.type.paramTypes.get(i);

                        if (!canAssign(argType, paramType)) {
                            // error: tip argumenta nije kompatibilan s tipom parametra
                            err(node);
                        }
                    }

                    // tip ← pov (povratni tip funkcije)
                    node.type = new Type(postfiks.type.returnType);
                    node.lvalue = false;
                } else if (node.children.size() == 2 &&
                        node.children.get(0).label.equals("<postfiks_izraz>") &&
                        (node.children.get(1).label.equals("OP_INC") ||
                                node.children.get(1).label.equals("OP_DEC"))) {
                    Node postfiks = node.children.get(0);
                    process(postfiks);
                    if (!postfiks.lvalue || !canAssign(postfiks.type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<lista argumenata>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                    process(node.children.get(0));
                    node.types = new ArrayList<>();
                    node.types.add(node.children.get(0).type);
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<lista_argumenata>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {

                    process(node.children.get(0));
                    process(node.children.get(2));

                    node.types = new ArrayList<>();
                    node.types.addAll(node.children.get(0).types);
                    node.types.add(node.children.get(2).type);
                }
                break;

            case "<unarni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<postfiks_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                }
                if (node.children.size() == 2 && (node.children.get(0).label.equals("OP_INC") || node.children.get(0).label.equals("OP_DEC")) && node.children.get(1).label.equals("<unarni_izraz>")) {
                    process(node.children.get(1));
                    if (!node.children.get(1).lvalue || !canAssign(node.children.get(1).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                if (node.children.size() == 2 && node.children.get(0).label.equals("<unarni_operator>") && node.children.get(1).label.equals("<cast_izraz>")) {
                    process(node.children.get(1));
                    if (!canAssign(node.children.get(1).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<unarni_operator>":
                break;

            case "<cast_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<unarni_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("L_ZAGRADA") && node.children.get(1).label.equals("<ime_tipa>") && node.children.get(2).label.equals("D_ZAGRADA") && node.children.get(3).label.equals("<cast_izraz>")) {
                    Node typeName = node.children.get(1);
                    Node castExp = node.children.get(3);

                    process(typeName);
                    process(castExp);

                    if (!canExplicitAssign(castExp.type, typeName.type)) {
                        err(node);
                    }

                    node.type = typeName.type;
                    node.lvalue = false;
                }
                break;

            case "<ime_tipa>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<specifikator_tipa>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                } else if (node.children.size() == 2 && node.children.get(0).label.equals("KR_CONST") && node.children.get(1).label.equals("<specifikator_tipa>")) {
                    Node spec = node.children.get(1);
                    process(spec);

                    if (spec.type.basic == Type.Basic.VOID) {
                        err(node);
                    }
                    node.type = new Type(spec.type);
                    node.type.isConst = true;
                }
                break;

            case "<specifikator_tipa>":
                if (node.children.size() == 1)
                    if (node.children.get(0).label.equals("KR_VOID"))
                        node.type = new Type(Type.Basic.VOID);
                    else if (node.children.get(0).label.equals("KR_INT"))
                        node.type = new Type(Type.Basic.INT);
                    else if (node.children.get(0).label.equals("KR_CHAR"))
                        node.type = new Type(Type.Basic.CHAR);
                    else {
                        err(node);
                    }
                break;

            case "<multiplikativni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<cast_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<multiplikativni_izraz>") &&
                        (node.children.get(1).label.equals("OP_PUTA") ||
                                node.children.get(1).label.equals("OP_DIJELI") ||
                                node.children.get(1).label.equals("OP_MOD")) &&
                        node.children.get(2).label.equals("<cast_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<aditivni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<multiplikativni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<aditivni_izraz>") &&
                        (node.children.get(1).label.equals("PLUS") ||
                                node.children.get(1).label.equals("MINUS")) &&
                        node.children.get(2).label.equals("<multiplikativni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<odnosni izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<aditivni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<odnosni_izraz>") &&
                        (node.children.get(1).label.equals("OP_LT") ||
                                node.children.get(1).label.equals("OP_GT") ||
                                node.children.get(1).label.equals("OP_LTE") ||
                                node.children.get(1).label.equals("OP_GTE")) &&
                        node.children.get(2).label.equals("<aditivni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<jednakosni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<odnosni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<jednakosni_izraz>") && (node.children.get(1).label.equals("OP_EQ") || node.children.get(1).label.equals("OP_NE")) && node.children.get(2).label.equals("<odnosni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<bin_i_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<jednakosni_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_i_izraz>") && node.children.get(1).label.equals("OP_BIN_I") && node.children.get(2).label.equals("<jednakosni_izraz")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    err(node);
                }
                break;

            case "<bin_xili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_i_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_xili_izraz>") && node.children.get(1).label.equals("OP_BIN_XILI") && node.children.get(2).label.equals("<bin_i_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    err(node);
                }
                break;

            case "<bin_ili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_xili_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_ili_izraz>") && node.children.get(1).label.equals("OP_BIN_ILI") && node.children.get(2).label.equals("<bin_xili_izraz")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    err(node);
                }
                break;

            case "<log_i_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_ili_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<log_i_izraz>") && node.children.get(1).label.equals("OP_I") && node.children.get(2).label.equals("<bin_ili_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    err(node);
                }
                break;

            case "<log_ili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<log_i_izraz>")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<log_ili_izraz>") && node.children.get(1).label.equals("OP_ILI") && node.children.get(2).label.equals("<log_i_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    err(node);
                }
                break;

            case "<izraz_pridruzivanja>":
                if (node.children.size() == 1) {
                    Node e = node.children.get(0);
                    process(e);
                    node.type = new Type(e.type);
                    node.lvalue = e.lvalue;
                } else {
                    Node postfiks = node.children.get(0);
                    Node izraz = node.children.get(2);

                    process(postfiks);

                    if (!postfiks.lvalue) {
                        err(node);
                    }

                    process(izraz);

                    if (!canAssign(izraz.type, postfiks.type)) {
                        err(node);
                    }
                    node.type = new Type(postfiks.type);
                    node.lvalue = false;
                }
                break;

            case "<izraz>":
                if (node.children.size() == 1) {
                    if (node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                        Node izraz_pri = node.children.get(0);
                        process(izraz_pri);
                        node.type = new Type(izraz_pri.type);
                        node.lvalue = izraz_pri.lvalue;
                    } else {
                        err(node);
                    }
                } else if (node.children.size() == 3) {
                    if (node.children.get(0).label.equals("<izraz>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {
                        Node izraz_pri = node.children.get(2);
                        process(node.children.get(0));
                        process(izraz_pri);
                        node.type = new Type(izraz_pri.type);
                        node.lvalue = false;
                    } else {
                        err(node);
                    }
                } else {
                    err(node);
                }
                break;

            //NAREDBENA STRUKTURA

            case "<slozena_naredba>":
                if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("L_VIT_ZAGRADA") &&
                        node.children.get(1).label.equals("<lista_naredbi>") &&
                        node.children.get(2).label.equals("D_VIT_ZAGRADA")) {
                    // novi scope
                    newScope();
                    process(node.children.get(1));
                    scopeStack.pop();
                } else if (node.children.size() == 4 &&
                        node.children.get(0).label.equals("L_VIT_ZAGRADA") &&
                        node.children.get(1).label.equals("<lista_deklaracija>") &&
                        node.children.get(2).label.equals("<lista_naredbi>") &&
                        node.children.get(3).label.equals("D_VIT_ZAGRADA")) {
                    // novi scope
                    newScope();
                    process(node.children.get(1));
                    process(node.children.get(2));
                    scopeStack.pop();
                }
                break;

            case "<lista naredbi>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<naredba>")) {
                    process(node.children.get(0));
                } else if (node.children.size() == 2 && node.children.get(0).label.equals("<lista_naredbi>") && node.children.get(1).label.equals("<naredba>")) {
                    process(node.children.get(0));
                    process(node.children.get(1));
                }
                break;

            case "<naredba>":
                if (node.children.size() == 1)
                    process(node.children.get(0));

                break;

            case "<izraz_naredba>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("TOCKAZAREZ"))
                    node.type = new Type(Type.Basic.INT);
                else if (node.children.size() == 2 && node.children.get(0).label.equals("<izraz>") && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    process(node.children.get(0));
                    node.type = new Type(node.children.get(0).type);
                } else {
                    err(node);
                }
                break;

            case "<naredba_grananja>":
                if (node.children.size() == 5 &&
                        node.children.get(0).label.equals("KR_IF") &&
                        node.children.get(1).label.equals("L_ZAGRADA") &&
                        node.children.get(2).label.equals("<izraz>") &&
                        node.children.get(3).label.equals("D_ZAGRADA") &&
                        node.children.get(4).label.equals("<naredba>")) {
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(4));
                } else if (node.children.size() == 7 &&
                        node.children.get(0).label.equals("KR_IF") &&
                        node.children.get(1).label.equals("L_ZAGRADA") &&
                        node.children.get(2).label.equals("<izraz>") &&
                        node.children.get(3).label.equals("D_ZAGRADA") &&
                        node.children.get(4).label.equals("<naredba>") &&
                        node.children.get(5).label.equals("KR_ELSE") &&
                        node.children.get(6).label.equals("<naredba>")) {
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(4));
                    process(node.children.get(6));
                }
                break;

            case "<naredba_petlje>":
                if (node.children.size() == 5 && node.children.get(0).label.equals("KR_WHILE") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz>") && node.children.get(3).label.equals("D_ZAGRADA") && node.children.get(4).label.equals("<naredba>")) {
                    Node izraz = node.children.get(2);
                    process(izraz);
                    if (!canAssign(izraz.type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    loopDepth++;
                    process(node.children.get(4));
                    loopDepth--;
                } else if (node.children.size() == 6 && node.children.get(0).label.equals("KR_FOR") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz_naredba>") && node.children.get(3).label.equals("<izraz_naredba>") && node.children.get(4).label.equals("D_ZAGRADA") && node.children.get(5).label.equals("<naredba>")) {
                    process(node.children.get(2));
                    process(node.children.get(3));
                    if (!canAssign(node.children.get(3).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    loopDepth++;
                    process(node.children.get(5));
                    loopDepth--;
                } else if (node.children.size() == 7 && node.children.get(0).label.equals("KR_FOR") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz_naredba>") && node.children.get(3).label.equals("<izraz_naredba>") && node.children.get(4).label.equals("<izraz>") && node.children.get(5).label.equals("D_ZAGRADA") && node.children.get(6).label.equals("<naredba>")) {
                    process(node.children.get(2));
                    process(node.children.get(3));
                    if (!canAssign(node.children.get(3).type, new Type(Type.Basic.INT))) {
                        err(node);
                    }
                    process(node.children.get(4));
                    loopDepth++;
                    process(node.children.get(6));
                    loopDepth--;
                } else {
                    err(node);
                }
                break;

            case "<naredba_skoka>":
                if (node.children.size() == 2 && (node.children.get(0).label.equals("KR_CONTINUE") || node.children.get(0).label.equals("KR_BREAK")) && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    if (loopDepth == 0) {
                        // error
                        err(node);
                    }
                }else if (node.children.size()==2 && node.children.get(0).label.equals("KR_RETURN") && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    Type returnType = functionStack.peek().returnType;
                    if (returnType.basic != Type.Basic.VOID) {
                        // error
                        err(node);
                    }
                }else if (node.children.size()==3 && node.children.get(0).label.equals("KR_RETURN") && node.children.get(1).label.equals("<izraz>") && node.children.get(2).label.equals("TOCKAZAREZ")) {
                    process(node.children.get(1));

                    if (!canAssign(node.children.get(1).type, functionStack.peek().returnType)) {
                        // error
                        err(node);
                    }
                }else{
                    // error
                    err(node);
                }
                break;

            case "<prijevodna_jedinica>":
                if(node.children.size()!= 1 && node.children.size()!= 2){
                    err(node);
                }
                if(!node.children.get(0).label.equals("<vanjska_deklaracija>") || !(node.children.get(0).label.equals("<prijevodna_jedinica>") && node.children.get(1).label.equals("<vanjska_deklaracija>"))){
                    err(node);
                }
                for(Node child: node.children)
                    process(child);
                break;

            case "<vanjska_deklaracija>":
                if (node.children.size()==1 && (node.children.get(0).label.equals("<deklaracija>") || node.children.get(0).label.equals("<definicija_funkcije>"))){
                    process(node.children.get(0));
                }else{
                    err(node);
                }
                break;



            // DEKLARACIJE I FUNKCIJE
            
            case "<definicija_funkcije>":
                if (node.children.size() == 6 &&
                        node.children.get(0).label.equals("<ime_tipa>") &&
                        node.children.get(1).label.equals("IDN") &&
                        node.children.get(2).label.equals("L_ZAGRADA") &&
                        node.children.get(3).label.equals("KR_VOID") &&
                        node.children.get(4).label.equals("D_ZAGRADA") &&
                        node.children.get(5).label.equals("<slozena_naredba>")) {
                    // 1. provjeri(<ime_tipa>)
                    process(node.children.get(0));

                    // 2. <ime_tipa>.tip != const(T)
                    if (node.children.get(0).type.isConst) {
                        // error
                        err(node);
                    }

                    String funcName = node.children.get(1).lexValue;
                    Type returnType = new Type(node.children.get(0).type);

                    // 3. ne postoji prije definirana funkcija imena IDN.ime
                    if (definedFunctions.contains(funcName)) {
                        // error
                        err(node);
                    }

                    // 4. ako postoji deklaracija imena IDN.ime u globalnom djelokrugu
                    // onda je pripadni tip te deklaracije funkcija(void -> <ime_tipa>.tip)

                    // Find declaration in global scope (scopeStack bottom)
                    scopeNode globalScope = scopeStack.firstElement();
                    boolean declared = false;
                    for (Symbol s : globalScope.localVariables) {
                        if (s.lexValue.equals(funcName)) {
                            declared = true;
                            if (!s.type.isFunction ||
                                    s.type.paramTypes.size() != 1 || // void is 1 param of type void
                                    s.type.paramTypes.get(0).basic != Type.Basic.VOID ||
                                    s.type.returnType.basic != returnType.basic) { // basic checks
                                // error
                                err(node);
                            }
                            break;
                        }
                    }

                    // 5. zabiljezi definiciju i deklaraciju funkcije
                    definedFunctions.add(funcName);
                    if (!declared) {
                        Type funcType = new Type(returnType);
                        funcType.isFunction = true;
                        funcType.paramTypes = new ArrayList<>();
                        funcType.paramTypes.add(new Type(Type.Basic.VOID)); // void param
                        funcType.returnType = returnType;

                        Symbol funcSymbol = new Symbol(funcName, funcType);
                        globalScope.localVariables.add(funcSymbol);
                    }

                    // Add return type to functionStack for checking return statements
                    functionStack.push(returnType);

                    // 6. provjeri(<slozena_naredba>)
                    process(node.children.get(5));

                    functionStack.pop();

                } else if (node.children.size() == 6 &&
                        node.children.get(0).label.equals("<ime_tipa>") &&
                        node.children.get(1).label.equals("IDN") &&
                        node.children.get(2).label.equals("L_ZAGRADA") &&
                        node.children.get(3).label.equals("<lista_parametara>") &&
                        node.children.get(4).label.equals("D_ZAGRADA") &&
                        node.children.get(5).label.equals("<slozena_naredba>")) {

                    // 1. provjeri(<ime_tipa>)
                    process(node.children.get(0));

                    // 2. <ime_tipa>.tip != const(T)
                    if (node.children.get(0).type.isConst) {
                        err(node);
                    }

                    String funcName = node.children.get(1).lexValue;
                    Type returnType = new Type(node.children.get(0).type);

                    // 3. ne postoji prije definirana funkcija imena IDN.ime
                    if (definedFunctions.contains(funcName)) {
                        err(node);
                    }

                    // Process parameters to get types
                    process(node.children.get(3));
                    List<Type> paramTypes = node.children.get(3).types;
                    List<String> paramNames = node.children.get(3).lexValues; // Need to capture names too

                     // 4. ako postoji deklaracija imena IDN.ime u globalnom djelokrugu ...
                    scopeNode globalScope = scopeStack.firstElement();
                    boolean declared = false;
                    for (Symbol s : globalScope.localVariables) {
                        if (s.lexValue.equals(funcName)) {
                            declared = true;
                            if (!s.type.isFunction ||
                                    s.type.paramTypes.size() != paramTypes.size() ||
                                    s.type.returnType.basic != returnType.basic) {
                                err(node);
                            }
                            // Check explicit parameter types match
                            for(int i=0; i<paramTypes.size(); ++i) {
                                if(s.type.paramTypes.get(i).basic != paramTypes.get(i).basic) { // simplistic type check
                                    err(node);
                                }
                            }
                            break;
                        }
                    }

                    // 5. zabiljezi definiciju i deklaraciju funkcije
                    definedFunctions.add(funcName);
                    if (!declared) {
                        Type funcType = new Type(returnType);
                        funcType.isFunction = true;
                        funcType.paramTypes = paramTypes;
                        funcType.returnType = returnType;

                        Symbol funcSymbol = new Symbol(funcName, funcType);
                        globalScope.localVariables.add(funcSymbol);
                    }

                    functionStack.push(returnType);

                    // Special handling for scope before processing block to insert parameters
                    // We need to 'peek' into the next scope or insert them into the scope create by slozena_naredba
                    // But slozena_naredba creates a new scope.
                    // The standard way is that parameters are in the function scope.
                    // Since slozena_naredba creates a new scope, we might need to pre-populate it?
                    // Or more likely, the parameters are effectively in the scope of the block.
                    // Given the structure, we can't easily inject into created scope inside slozena_naredba.
                    // Modifications to ensure params are visible in the function body:

                    // Simpler approach: Create a temporary scope here, add params, then process slozena_naredba
                    // But slozena_naredba does `newScope()`.
                    // If we do newScope here, then slozena_naredba does another, we get nesting.

                    // Correct logic: The function body is a block. Parameters are local to that block.
                    // But we can't edit slozena_naredba.
                    // Let's look at how slozena_naredba works. It creates a new scope.
                    // We can employ a trick: Push a scope, add params, then let slozena_naredba push ANOTHER scope?
                    // No, parameters should be in the immediate scope of the function body.

                    // Wait, the instructions say:
                    // "Djelokrug definiran slozenom naredbom, tj. tijelom funkcije, pridruzuje se definiciji funkcije"

                    // Let's hack it: Prepare the parameters to be added to the NEXT scope created.
                    // Or we can manually trigger the scope creation here and avoid it in slozena_naredba? No, can't change that node logic easily without messing other things.

                    // Actually, if we look at typical C scope rules, function parameters are in the function scope.
                    // The body block adds another scope? Usually not, or it's the SAME scope.
                    // But here slozena_naredba definitely calls newScope().
                    // If we add params to the current global scope? No.

                    // A common pattern in these labs:
                    // Create a scope, add params.
                    // Then parse the block. BUT the block parser creates a scope.
                    // Is it possible to add them to the scope created by slozena_naredba?
                    // We can pre-calculate them and put them in a static list `pendingParameters`?

                    // Or, we can modify `slozena_naredba` handling to support context.
                    // But I strictly need to implement `process` for `definicija_funkcije` here.

                    // Let's assume for now we push a scope here with parameters.
                    // Then slozena_naredba pushes another scope.
                    // Then the variables inside are in a sub-scope of parameters. This works for visibility!
                    // If I declare `int x` in body, and `int x` is a param, it shadows it. That is valid C?
                    // Actually in C you cannot redeclare a parameter in the top-level block of the function.
                    // "6.3.2. ... specific structure checks..."

                    // Let's just push a special scope for parameters.
                    newScope();
                    scopeNode paramScope = scopeStack.peek();
                    for(int i=0; i<paramNames.size(); ++i) {
                         Symbol p = new Symbol(paramNames.get(i), paramTypes.get(i));
                         p.lvalue = true; // params are lvalues
                         paramScope.localVariables.add(p);
                    }

                    // Now process body. It will create a sub-scope.
                    process(node.children.get(5));

                    // Pop param scope
                    scopeStack.pop();

                    functionStack.pop();
                }
                break;

            case "<lista_parametara>":
                if (node.children.size()==1 && node.children.get(0).label.equals("<deklaracija_parametra>")){
                    process(node.children.get(0));
                    node.types = new ArrayList<>();
                    node.types.add(node.children.get(0).type);
                    node.lexValues = new ArrayList<>();
                    node.lexValues.add(node.children.get(0).lexValue);
                }else if (node.children.size()==3 && node.children.get(0).label.equals("<lista_parametara>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<deklaracija_parametra>")){
                    process(node.children.get(0));
                    process(node.children.get(2));
                    if (node.children.get(0).lexValues.contains(node.children.get(2).lexValue)){
                        err(node);
                    }
                    node.types = new ArrayList<>();
                    node.types.addAll(node.children.get(0).types);
                    node.types.add(node.children.get(2).type);
                    node.lexValues = new ArrayList<>();
                    node.lexValues.addAll(node.children.get(0).lexValues);
                    node.lexValues.add(node.children.get(2).lexValue);
                }else{
                    err(node);
                }
                break;

            case "<deklaracija_parametra>":
                if (node.children.size()==2 && node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("IDN")){
                    process(node.children.get(0));
                    if (node.children.get(0).type.basic==Type.Basic.VOID){
                        err(node);
                    }
                    node.type=node.children.get(0).type;
                    node.lexValue=node.children.get(1).lexValue;
                }else if (node.children.size()==4 && node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("IDN") && node.children.get(2).label.equals("L_UGL_ZAGRADA") && node.children.get(3).label.equals("D_UGL_ZAGRADA")){
                    process(node.children.get(0));
                    if (node.children.get(0).type.basic==Type.Basic.VOID){
                        err(node);
                    }
                    Type base = node.children.get(0).type;
                    Type t = new Type(base.basic);
                    t.isSequence = true;
                    node.type = t;
                    node.lexValue=node.children.get(1).lexValue;
                }else{
                    err(node);
                }
                break;

            case "<lista_deklaracija>":
                if (node.children.size()==1 && node.children.get(0).label.equals("<deklaracija>")){
                    process(node.children.get(0));
                }else if (node.children.size()==2 && node.children.get(0).label.equals("<lista_deklaracija>") && node.children.get(1).label.equals("<deklaracija>")){
                    process(node.children.get(0));
                    process(node.children.get(1));
                }else{
                    err(node);
                }
                break;

            case "<deklaracija>":
                if (node.children.size() != 3) {
                    if (node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("<lista_init_deklaratora>") && node.children.get(2).label.equals("TOCKAZAREZ")) {
                        Node imeTipa = node.children.get(0);
                        Node listaInitDek = node.children.get(1);

                        process(imeTipa);

                        listaInitDek.itype = new Type(imeTipa.type);
                        process(listaInitDek);
                        break;
                    } else {
                        err(node);
                    }
                } else {
                    err(node);
                }
                break;

            case "<lista_init_deklaratora>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<init_deklarator>")) {
                    node.children.get(0).itype=node.itype;
                    process(node.children.get(0));
                }else if (node.children.size()==3 && node.children.get(0).label.equals("<lista_init_deklaratora>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<init_deklarator>")){
                    node.children.get(0).itype=node.itype;
                    process(node.children.get(0));
                    node.children.get(2).itype=node.itype;
                    process(node.children.get(2));
                }else{
                    err(node);
                }
                break;

            case "<init_deklarator>":
                node.children.get(0).itype = new Type(node.itype);
                process(node.children.get(0));

                if (node.children.size() == 1) {
                    if (node.children.get(0).type.isConst){
                        err(node);
                    }
                    break;
                }

                process(node.children.get(2));

                Type varType = new Type(node.children.get(0).type);
                Node init = node.children.get(2);

                if (!varType.isSequence) {
                    if (!canAssign(init.type, varType)) {
                        err(node);
                    }
                } else {
                    if (init.types.size() > varType.elemNr){
                        err(node);
                    }

                    for (Type t : init.types) {
                        if (!canAssign(t, new Type(varType.basic))) {
                            err(node);
                        }
                    }
                }
                break;

            case "<izravni_deklarator>":
                if (node.children.size()==1 && node.children.get(0).label.equals("IDN")){
                    if (node.itype.basic==Type.Basic.VOID){
                        // error
                        err(node);
                    }
                    scopeNode curr = scopeStack.peek();
                    for(Symbol s: curr.localVariables){
                        if(s.lexValue.equals(node.children.get(0).lexValue)){
                            err(node);
                            break;
                        }
                    }
                    curr.localVariables.add(new Symbol(node.children.get(0).lexValue, node.children.get(0).type));
                    node.type = new Type(node.itype);
                }else if (node.children.size()==4 && node.children.get(0).label.equals("IDN") && node.children.get(1).label.equals("L_UGL_ZAGRADA") && node.children.get(2).label.equals("BROJ") && node.children.get(3).label.equals("D_UGL_ZAGRADA")){
                    if (node.itype.basic==Type.Basic.VOID){
                        err(node);
                    }
                    scopeNode curr = scopeStack.peek();
                    for(Symbol s: curr.localVariables){
                        if(s.lexValue.equals(node.children.get(0).lexValue)){
                            err(node);
                            break;
                        }
                    }
                    String str = node.children.get(2).lexValue;
                    if (Integer.parseInt(str) < 1 || Integer.parseInt(str) > 1024) {
                        err(node);
                    }
                    Type t = new Type(node.itype.basic);
                    t.isSequence = true;
                    t.elemNr = Integer.parseInt(str);

                    node.type = new Type(t);
                    curr.localVariables.add(new Symbol(node.children.get(0).lexValue, t));
                }else if (node.children.size()==4 && node.children.get(0).label.equals("IDN") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("KR_VOID") && node.children.get(3).label.equals("D_ZAGRADA")){
                    scopeNode curr = scopeStack.peek();
                    boolean found = false;
                    for(Symbol s: curr.localVariables){
                        if(s.lexValue.equals(node.children.get(0).lexValue)){
                            s.type.isFunction = true;
                            s.type.paramTypes = new ArrayList<>();
                            s.type.paramTypes.add(new Type(Type.Basic.VOID));
                            s.type.returnType = new Type(node.itype);
                            found = true;
                            break;
                        }
                    }
                    if(!found){
                        Symbol s = new  Symbol(node.children.get(0).label, node.children.get(0).type);
                        s.type.isFunction = true;
                        s.type.paramTypes = new ArrayList<>();
                        s.type.paramTypes.add(new Type(Type.Basic.VOID));
                        s.type.returnType = new Type(node.itype);
                        curr.localVariables.add(s);
                    }
                }else if (node.children.size()==4 && node.children.get(0).label.equals("IDN") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<lista_parametara>") && node.children.get(3).label.equals("D_ZAGRADA")){
                    process(node.children.get(2));
                    scopeNode curr = scopeStack.peek();
                    boolean found = false;
                    for(Symbol s: curr.localVariables){
                        if(s.lexValue.equals(node.children.get(0).lexValue)){
                            s.type.isFunction = true;
                            s.type.paramTypes = node.children.get(2).types;
                            s.type.returnType = new Type(node.itype);
                            found = true;
                            break;
                        }
                    }
                    if(!found){
                        Symbol s = new  Symbol(node.children.get(0).label, node.children.get(0).type);
                        s.type.isFunction = true;
                        s.type.paramTypes = node.children.get(2).types;
                        s.type.returnType = new Type(node.itype);
                        curr.localVariables.add(s);
                    }
                }else{
                    err(node);
                }
                break;

            case "<inicijalizator>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                    process(node.children.get(0));
                    if (node.children.get(0).label.equals("NIZ_ZNAKOVA")){
                        String s = node.children.get(0).lexValue;
                        for (int i = 0; i < s.length()+1; ++i) {
                            node.types.add(new Type(Type.Basic.CHAR));
                        }

                    }else{
                        node.type = new Type(node.children.get(0).type);
                    }
                }
                break;

            case "<lista_izraza_pridruzivanja>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                    process(node.children.get(0));
                    node.types = new ArrayList<>();
                    node.types.add(node.children.get(0).type);
                }else if (node.children.size()==3 && node.children.get(0).label.equals("<lista_izraza_pridruzivanja>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {
                    process(node.children.get(0));
                    process(node.children.get(2));
                    node.types = new ArrayList<>();
                    node.types.addAll(node.children.get(0).types);
                    node.types.add(node.children.get(2).type);
                }else{
                    err(node);
                }
                break;

            default:
                return;        
        }

        for (Node child : node.children)
            process(child);
        }

    static void err(Node node) {
        System.out.print(node.label + " ::=");
        for (Node child : node.children) {
            System.out.print(" ");
            if (child.label.startsWith("<")) {
                System.out.print(child.label);
            } else {
                System.out.print(child.label + "(" + child.row + "," + child.lexValue + ")");
            }
        }
        System.out.println();
        System.exit(0);
    }

    public static void main(String[] args) {
        Node root = null;
        try {
            root = loadTree();
        } catch (IOException e) {
            e.printStackTrace();
        }

        // Initialize global scope
        scopeStack.push(new scopeNode(null));

        process(root);
        checkMain();
    }

    static void checkMain() {
        boolean foundReference = false;
        scopeNode global = scopeStack.pop();
        while(!scopeStack.isEmpty())
            global = scopeStack.pop();

        for (Symbol s : global.localVariables) {
            if (s.lexValue.equals("main") && s.type.isFunction &&
                s.type.returnType.basic == Type.Basic.INT &&
                s.type.paramTypes.size() == 1 &&
                s.type.paramTypes.get(0).basic == Type.Basic.VOID) {
                foundReference = true;
                break;
            }
        }

        if (!foundReference || !definedFunctions.contains("main")) {
             System.out.println("main");
             System.exit(0);
        }

        // Check for declared but undefined functions
        for (Symbol s : global.localVariables) {
            if (s.type.isFunction) {
                // If it is declared (in symbol table) but not defined (in definedFunctions set)
                if (!definedFunctions.contains(s.lexValue)) {
                    System.out.println("funkcija");
                    System.exit(0);
                }
            }
        }
    }
}
