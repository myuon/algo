pub enum Token {
    Number(i32),
    Symbol(String),
}

#[derive(PartialEq, Debug)]
pub enum Operator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
}

impl Operator {
    fn from_str(op: &str) -> Self {
        match op {
            "+" => Operator::Add,
            "-" => Operator::Subtract,
            "*" => Operator::Multiply,
            "/" => Operator::Divide,
            "==" => Operator::Equal,
            _ => panic!("unsupported operator"),
        }
    }

    fn precedence(&self) -> i32 {
        use Operator::*;

        match self {
            Equal => 0,
            Add => 1,
            Subtract => 1,
            Multiply => 2,
            Divide => 2,
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum Expr {
    Op(Operator, Box<Expr>, Box<Expr>),
    NumLit(i32),
    OpLit(Operator),
}

fn squash(stack: &mut Vec<Expr>) {
    while stack.len() >= 3 {
        let e1 = stack.pop().unwrap();
        let op = match stack.pop().unwrap() {
            Expr::OpLit(op) => op,
            _ => panic!("unexpected token"),
        };
        let e2 = stack.pop().unwrap();
        stack.push(Expr::Op(op, Box::new(e2), Box::new(e1)));
    }
}

fn parse(tokens: Vec<Token>) -> Expr {
    let mut stack = Vec::new();
    let mut min_precd = 0;

    for token in tokens {
        match token {
            Token::Number(i) => stack.push(Expr::NumLit(i)),
            Token::Symbol(u) => {
                let k = Operator::from_str(&u);

                if k.precedence() < min_precd {
                    squash(&mut stack);
                }

                min_precd = k.precedence();
                stack.push(Expr::OpLit(k));
            }
        }
    }

    squash(&mut stack);
    stack.pop().unwrap()
}

#[test]
fn it_should_parse() {
    assert_eq!(
        parse(vec![
            Token::Number(2),
            Token::Symbol("+".to_string()),
            Token::Number(3),
            Token::Symbol("*".to_string()),
            Token::Number(4),
            Token::Symbol("+".to_string()),
            Token::Number(5),
            Token::Symbol("==".to_string()),
            Token::Number(19),
        ]),
        Expr::Op(
            Operator::Equal,
            Box::new(Expr::Op(
                Operator::Add,
                Box::new(Expr::Op(
                    Operator::Add,
                    Box::new(Expr::NumLit(2)),
                    Box::new(Expr::Op(
                        Operator::Multiply,
                        Box::new(Expr::NumLit(3)),
                        Box::new(Expr::NumLit(4))
                    ))
                )),
                Box::new(Expr::NumLit(5))
            )),
            Box::new(Expr::NumLit(19))
        )
    );
}
