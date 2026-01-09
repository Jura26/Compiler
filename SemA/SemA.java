package SemA;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.util.*;

public class SemA {
    static int loopDepth = 0;
    static int nodeId = 0;
    static int scopeNodeId = 0;
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

        Type(Basic basic) {
            this.basic = basic;
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
                        //error
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
                    node.type = node.children.get(1).type;
                    node.lvalue = node.children.get(1).lvalue;
                    process(node.children.get(1));
                }
                break;

            case "<postfiks izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<primarni_izraz>")) {
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                    process(node.children.get(0));
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_UGL_ZAGRADA") && node.children.get(2).label.equals("<izraz>") && node.children.get(3).label.equals("D_UGL_ZAGRADA")) {
                    Node postfiks = node.children.get(0);
                    Node izraz = node.children.get(2);

                    process(postfiks);

                    if (postfiks.type == null || !postfiks.type.isSequence) {
                        // error
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
                    }
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("D_ZAGRADA")) {
                    Node postfiks = node.children.get(0);

                    // 1. provjeri(<postfiks_izraz>)
                    process(postfiks);

                    // 2. <postfiks_izraz>.tip = funkcija(void → pov)
                    if (postfiks.type == null || !postfiks.type.isFunction) {
                        // error
                    }

                    node.type = postfiks.type.returnType;
                    node.lvalue = false;
                } else if (node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<lista_argumenata>") && node.children.get(3).label.equals("D_ZAGRADA")) {
                    Node postfiks = node.children.get(0);
                    Node listaArgumenata = node.children.get(2);

                    process(postfiks);

                    process(listaArgumenata);

                    if (postfiks.type == null || !postfiks.type.isFunction) {
                        // error
                    }

                    // Provjeri da broj argumenata odgovara broju parametara
                    if (postfiks.type.paramTypes == null || listaArgumenata.types == null ||
                            postfiks.type.paramTypes.size() != listaArgumenata.types.size()) {
                        // error: broj argumenata ne odgovara broju parametara
                    }

                    // Provjeri da su tipovi argumenata kompatibilni s tipovima parametara (redom)
                    for (int i = 0; i < postfiks.type.paramTypes.size(); i++) {
                        Type argType = listaArgumenata.types.get(i);
                        Type paramType = postfiks.type.paramTypes.get(i);

                        if (!canAssign(argType, paramType)) {
                            // error: tip argumenta nije kompatibilan s tipom parametra
                        }
                    }

                    // tip ← pov (povratni tip funkcije)
                    node.type = postfiks.type.returnType;
                    node.lvalue = false;
                } else if (node.children.size() == 2 &&
                        node.children.get(0).label.equals("<postfiks_izraz>") &&
                        (node.children.get(1).label.equals("OP_INC") ||
                                node.children.get(1).label.equals("OP_DEC"))) {
                    Node postfiks = node.children.get(0);
                    process(postfiks);
                    if (!postfiks.lvalue || !canAssign(postfiks.type, new Type(Type.Basic.INT))) {
                        //error
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
                        //error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                if (node.children.size() == 2 && node.children.get(0).label.equals("<unarni_operator>") && node.children.get(1).label.equals("<cast_izraz>")) {
                    process(node.children.get(1));
                    if (!canAssign(node.children.get(1).type, new Type(Type.Basic.INT))) {
                        //error
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
                        // error
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
                        //error()
                    }
                    node.type = spec.type;
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
                        //error
                    }
                break;

            case "<multiplikativni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<cast_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<multiplikativni_izraz>") &&
                        (node.children.get(1).label.equals("OP_PUTA") ||
                                node.children.get(1).label.equals("OP_DIJELI") ||
                                node.children.get(1).label.equals("OP_MOD")) &&
                        node.children.get(2).label.equals("<cast_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        //error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        //error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<aditivni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<multiplikativni_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 &&
                        node.children.get(0).label.equals("<aditivni_izraz>") &&
                        (node.children.get(1).label.equals("PLUS") ||
                                node.children.get(1).label.equals("MINUS")) &&
                        node.children.get(2).label.equals("<multiplikativni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        //error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        //error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<odnosni izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<aditivni_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
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
                        //error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        //error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<jednakosni_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<odnosni_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<jednakosni_izraz>") && (node.children.get(1).label.equals("OP_EQ") || node.children.get(1).label.equals("OP_NE")) && node.children.get(2).label.equals("<odnosni_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                break;

            case "<bin_i_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<jednakosni_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_i_izraz>") && node.children.get(1).label.equals("OP_BIN_I") && node.children.get(2).label.equals("<jednakosni_izraz")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    //error
                }
                break;

            case "<bin_xili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_i_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_xili_izraz>") && node.children.get(1).label.equals("OP_BIN_XILI") && node.children.get(2).label.equals("<bin_i_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    //error
                }
                break;

            case "<bin_ili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_xili_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<bin_ili_izraz>") && node.children.get(1).label.equals("OP_BIN_ILI") && node.children.get(2).label.equals("<bin_xili_izraz")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    //error
                }
                break;

            case "<log_i_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<bin_ili_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<log_i_izraz>") && node.children.get(1).label.equals("OP_I") && node.children.get(2).label.equals("<bin_ili_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    //error
                }
                break;

            case "<log_ili_izraz>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<log_i_izraz>")) {
                    process(node.children.get(0));
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                } else if (node.children.size() == 3 && node.children.get(0).label.equals("<log_ili_izraz>") && node.children.get(1).label.equals("OP_ILI") && node.children.get(2).label.equals("<log_i_izraz>")) {
                    process(node.children.get(0));
                    if (!canAssign(node.children.get(0).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    process(node.children.get(2));
                    if (!canAssign(node.children.get(2).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                } else {
                    //error
                }
                break;

            case "<izraz_pridruzivanja>":
                if (node.children.size() == 1) {
                    Node e = node.children.get(0);
                    process(e);
                    node.type = e.type;
                    node.lvalue = e.lvalue;
                } else {
                    Node postfiks = node.children.get(0);
                    Node izraz = node.children.get(2);

                    process(postfiks);

                    if (!postfiks.lvalue) {
                        //error
                    }

                    process(izraz);

                    if (!canAssign(izraz.type, postfiks.type)) {
                        //error
                    }
                    node.type = postfiks.type;
                    node.lvalue = false;
                }
                break;

            case "<izraz>":
                if (node.children.size() == 1) {
                    if (node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
                        Node izraz_pri = node.children.get(0);
                        process(izraz_pri);
                        node.type = izraz_pri.type;
                        node.lvalue = izraz_pri.lvalue;
                    } else {
                        //error
                    }
                } else if (node.children.size() == 3) {
                    if (node.children.get(0).label.equals("<izraz>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {
                        Node izraz_pri = node.children.get(2);
                        process(node.children.get(0));
                        process(izraz_pri);
                        node.type = izraz_pri.type;
                        node.lvalue = false;
                    } else {
                        //error
                    }
                } else {
                    //error
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
                } else if (node.children.size() == 4 &&
                        node.children.get(0).label.equals("L_VIT_ZAGRADA") &&
                        node.children.get(1).label.equals("<lista_deklaracija>") &&
                        node.children.get(2).label.equals("<lista_naredbi>") &&
                        node.children.get(3).label.equals("D_VIT_ZAGRADA")) {
                    // novi scope
                    newScope();
                    process(node.children.get(1));
                    process(node.children.get(2));
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
                    node.type = node.children.get(0).type;
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
                        //error
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
                        //error
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
                        // error
                    }
                    loopDepth++;
                    process(node.children.get(4));
                    loopDepth--;
                } else if (node.children.size() == 6 && node.children.get(0).label.equals("KR_FOR") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz_naredba>") && node.children.get(3).label.equals("<izraz_naredba>") && node.children.get(4).label.equals("D_ZAGRADA") && node.children.get(5).label.equals("<naredba>")) {
                    process(node.children.get(2));
                    process(node.children.get(3));
                    if (!canAssign(node.children.get(3).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    loopDepth++;
                    process(node.children.get(5));
                    loopDepth--;
                } else if (node.children.size() == 7 && node.children.get(0).label.equals("KR_FOR") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<izraz_naredba>") && node.children.get(3).label.equals("<izraz_naredba>") && node.children.get(4).label.equals("<izraz>") && node.children.get(5).label.equals("D_ZAGRADA") && node.children.get(6).label.equals("<naredba>")) {
                    process(node.children.get(2));
                    process(node.children.get(3));
                    if (!canAssign(node.children.get(3).type, new Type(Type.Basic.INT))) {
                        // error
                    }
                    process(node.children.get(4));
                    loopDepth++;
                    process(node.children.get(6));
                    loopDepth--;
                } else {
                    // error
                }
                break;

            case "<naredba_skoka>":
                if (node.children.size() == 2 && (node.children.get(0).label.equals("KR_CONTINUE") || node.children.get(0).label.equals("KR_BREAK")) && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    if (loopDepth == 0) {
                        // error
                    }
                }else if (node.children.size()==2 && node.children.get(0).label.equals("KR_RETURN") && node.children.get(1).label.equals("TOCKAZAREZ")) {
                    Type returnType = functionStack.peek().returnType;
                    if (returnType.basic != Type.Basic.VOID) {
                        // error
                    }
                }else if (node.children.size()==3 && node.children.get(0).label.equals("KR_RETURN") && node.children.get(1).label.equals("<izraz>") && node.children.get(2).label.equals("TOCKAZAREZ")) {
                    process(node.children.get(1));

                    if (!canAssign(node.children.get(1).type, functionStack.peek().returnType)) {
                        // error
                    }
                }else{
                    // error
                }
                break;

            case "<prijevodna_jedinica>":
                if(node.children.size()!= 1 && node.children.size()!= 2){}
                //error
                if(!node.children.get(0).label.equals("<vanjska_deklaracija>") || !(node.children.get(0).label.equals("<prijevodna_jedinica>") && node.children.get(1).label.equals("<vanjska_deklaracija>"))){}
                //error
                for(Node child: node.children)
                    process(child);
                break;

            case "<vanjska_deklaracija>":
                if (node.children.size()==1 && (node.children.get(0).label.equals("<deklaracija>") || node.children.get(0).label.equals("<definicija_funkcije>"))){
                    process(node.children.get(0));
                }else{
                    //error
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
                        node.children.get(5).label.equals("<slozena_naredba>"))
                {
                    process(node.children.get(0));
                    if(node.children.get(0).type.isConst){
                        //error
                    }
                    scopeNode curr = scopeStack.peek();
                    while(curr.parent != null){
                        for(Symbol s: curr.localVariables){
                            if(s.lexValue.equals(node.lexValue)){
                                //error
                                break;
                            }
                        }
                        curr = curr.parent;
                    }
                    for(Symbol s: curr.localVariables){
                        if(s.lexValue.equals(node.lexValue)){
                            node.type.isFunction = true;
                            node.type.returnType = node.children.get(0).type;
                            node.type.paramTypes = new ArrayList<>();
                            node.type.paramTypes.add(new Type(Type.Basic.VOID));
                        }
                    }
                    Symbol newS = new Symbol(node.label, node.type); // neznam str 66

                    process(node.children.get(5));

                }



            case "<deklaracija>":
                if (node.children.size() != 3) {
                    if (node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("<lista_init_deklaratora>") && node.children.get(2).label.equals("TOCKAZAREZ")) {
                        Node imeTipa = node.children.get(0);
                        Node listaInitDek = node.children.get(1);

                        process(imeTipa);

                        listaInitDek.itype = imeTipa.type;
                        process(listaInitDek);
                        break;
                    } else {
                        //error
                    }
                } else {
                    //error
                }
                break;

            case "<inicijalizator>":
                if (node.children.size() == 1 && node.children.get(0).label.equals("<izraz_pridruzivanja>")) {
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
                    //error
                }
                break;

            default:
                return;        
        }

        for (Node child : node.children)
            process(child);
        }

    public static void main(String[] args) {
        Node root = null;
        try {
            root = loadTree();
        } catch (IOException e) {
            e.printStackTrace();
        }

        ispisiStablo(root, 0);
        process(root);
    }
}
