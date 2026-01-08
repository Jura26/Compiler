package SemA;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.reflect.Type;
import java.util.*;

public class SemA {

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
        List<Type> tipovi = null; // lista tipova argumenata (za <lista_argumenata>)

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


    static void process(Node node){
        switch(node.label) {
            case "<primarni_izraz>":
                if(node.children.isEmpty()){
                    //error
                }
                if(node.children.size() == 1 && node.children.get(0).label.equals("IDN")){
                    boolean found = false;
                    ArrayList<scopeNode> list = new ArrayList<>();
                    while(!found || !scopeStack.isEmpty()) {
                        list.add(scopeStack.pop());
                        for (Symbol s : list.get(list.size() - 1).localVariables)
                            if (s.label.equals("IDN") && s.lexValue.equals(node.children.get(0).lexValue)){
                                found = true;

                                node.type = s.type;
                                node.lvalue = s.lvalue;
                            }
                    }
                    for(int i = list.size() - 1; i >= 0; i--)
                        scopeStack.push(list.remove(i));

                    if(!found){
                        //error
                    }
                }
                else if(node.children.size() == 1 && node.children.get(0).label.equals("BROJ")){
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
                }
                else if(node.children.size() == 1 && node.children.get(0).label.equals("ZNAK")){
                    node.type = new Type(Type.Basic.CHAR);
                    node.lvalue = false;
                }
                else if(node.children.size() == 1 && node.children.get(0).label.equals("NIZ_ZNAKOVA")){
                    node.type = new Type(Type.Basic.CHAR);
                    node.type.isSequence = true;
                    node.type.isConst = true;
                    node.lvalue = false;
                }
                else if(node.children.size() == 3 && node.children.get(0).label.equals("L_ZAGRADA") && node.children.get(1).label.equals("<izraz>") && node.children.get(2).label.equals("D_ZAGRADA")){
                    node.type = node.children.get(1).type;
                    node.lvalue = node.children.get(1).lvalue;
                    process(node.children.get(1));
                }
                //error
                break;

            case "<postfiks izraz>":
                if(node.children.size() == 1 && node.children.get(0).label.equals("<primarni_izraz>")){
                    node.type = node.children.get(0).type;
                    node.lvalue = node.children.get(0).lvalue;
                    process(node.children.get(0));
                }
                else if(node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") &&  node.children.get(1).label.equals("L_UGL_ZAGRADA") && node.children.get(2).label.equals("<izraz>") && node.children.get(3).label.equals("D_UGL_ZAGRADA")){
                    Node postfiks = node.children.get(0);
                    Node izraz = node.children.get(2);

                    // 1. provjeri(<postfiks_izraz>)
                    process(postfiks);

                    // 2. <postfiks_izraz>.tip = niz(X)
                    if (postfiks.type == null || !postfiks.type.isSequence) {
                        // error: indexing non-array type
                    }

                    Type elementType = new Type(postfiks.type.basic);
                    elementType.isSequence = false;
                    elementType.isConst = postfiks.type.isConst;
                    node.type = elementType;

                    node.lvalue = !elementType.isConst;

                    process(izraz);

                    Type intType = new Type(Type.Basic.INT);
                    if (izraz.type == null || !canAssign(izraz.type, intType)) {
                        // error: index not compatible with int
                    }
                }
                else if(node.children.size() == 3 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("D_ZAGRADA")){
                    Node postfiks = node.children.get(0);

                    // 1. provjeri(<postfiks_izraz>)
                    process(postfiks);

                    // 2. <postfiks_izraz>.tip = funkcija(void → pov)
                    if (postfiks.type == null || !postfiks.type.isFunction) {
                        // error: not a function type
                    }

                    // tip ← pov (povratni tip funkcije)
                    node.type = postfiks.type.returnType;
                    node.lvalue = false;
                }
                else if(node.children.size() == 4 && node.children.get(0).label.equals("<postfiks_izraz>") && node.children.get(1).label.equals("L_ZAGRADA") && node.children.get(2).label.equals("<lista_argumenata>") && node.children.get(3).label.equals("D_ZAGRADA")){
                    Node postfiks = node.children.get(0);
                    Node listaArgumenata = node.children.get(2);

                    // 1. provjeri(<postfiks_izraz>)
                    process(postfiks);

                    // 2. provjeri(<lista_argumenata>)
                    process(listaArgumenata);

                    // 3. <postfiks_izraz>.tip = funkcija(params → pov)
                    if (postfiks.type == null || !postfiks.type.isFunction) {
                        // error: not a function type
                    }

                    // Provjeri da broj argumenata odgovara broju parametara
                    if (postfiks.type.paramTypes == null || listaArgumenata.tipovi == null ||
                        postfiks.type.paramTypes.size() != listaArgumenata.tipovi.size()) {
                        // error: broj argumenata ne odgovara broju parametara
                    }

                    // Provjeri da su tipovi argumenata kompatibilni s tipovima parametara (redom)
                    for (int i = 0; i < postfiks.type.paramTypes.size(); i++) {
                        Type argType = listaArgumenata.tipovi.get(i);
                        Type paramType = postfiks.type.paramTypes.get(i);

                        if (!canAssign(argType, paramType)) {
                            // error: tip argumenta nije kompatibilan s tipom parametra
                        }
                    }

                    // tip ← pov (povratni tip funkcije)
                    node.type = postfiks.type.returnType;
                    node.lvalue = false;
                }
                else if(node.children.size() == 2 &&
                        node.children.get(0).label.equals("<postfiks_izraz>") &&
                        (node.children.get(1).label.equals("OP_INC") ||
                                node.children.get(1).label.equals("OP_DEC")))
                {
                    Node postfiks = node.children.get(0);
                    process(postfiks);
                    if(!postfiks.lvalue || !canAssign(postfiks.type, new Type(Type.Basic.INT))){
                        //error
                    }
                    node.type = new Type(Type.Basic.INT);
                    node.lvalue = false;
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

            case "<deklaracija>":
                if (node.children.size()!=3){
                    if (node.children.get(0).label.equals("<ime_tipa>") && node.children.get(1).label.equals("<lista_init_deklaratora>") && node.children.get(2).label.equals("TOCKAZAREZ")) {
                        Node imeTipa = node.children.get(0);
                        Node listaInitDek = node.children.get(1);

                        process(imeTipa);

                        listaInitDek.itype = imeTipa.type;
                        process(listaInitDek);
                        break;
                    }else{
                        //error
                    }
                }else{
                    //error
                }

            case "<ime_tipa>":
                if (node.children.size()==1){
                    Node spec = node.children.get(0);
                    node.type = spec.type;
                    process(spec);
                    return;
                }else if (node.children.size()==2){
                    Node spec = node.children.get(1);
                    Type t = new Type(spec.type.basic);
                    t.isSequence = spec.type.isSequence;
                    t.isConst = true;

                    node.type = t;

                    if (spec.type.basic == Type.Basic.VOID){
                        //error()
                    }
                }

            case "<specifikator_tipa>":
                if (node.children.get(0).equals("KR_VOID")){
                    node.type = new Type(Type.Basic.VOID);
                }else if (node.children.get(0).equals("KR_INT")){
                    node.type = new Type(Type.Basic.INT);
                }else if (node.children.get(0).equals("KR_CHAR")){
                    node.type = new Type(Type.Basic.CHAR);
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
                if (node.children.size()==1){
                    if (node.children.get(0).label.equals("<izraz_pridruzivanja>")){
                        Node izraz_pri = node.children.get(0);
                        process(izraz_pri);
                        node.type = izraz_pri.type;
                        node.lvalue = izraz_pri.lvalue;
                    }else{
                        //error
                    }
                }else if (node.children.size()==3){
                    if (node.children.get(0).label.equals("<izraz>") && node.children.get(1).label.equals("ZAREZ") && node.children.get(2).label.equals("<izraz_pridruzivanja>")) {
                        Node izraz_pri = node.children.get(2);
                        process(node.children.get(0));
                        process(izraz_pri);
                        node.type = izraz_pri.type;
                        node.lvalue = false;
                    }else{
                        //error
                    }
                }else{
                    //error
                }
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
