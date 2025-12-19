# ECS 189C: Software Correctness - Winter Quarter 2026

## Contents

1. [Welcome and Course Information](#welcome-and-course-information)
2. [Lectures](#lectures)
3. [Course Description](#course-description)
4. [Schedule](#schedule)
5. [Grade Breakdown](#grade-breakdown)
6. [Policies](#policies)
7. [Disclaimers](#disclaimers)
8. [Contact and Office Hours](#contact-and-office-hours)

## Welcome and Course Information

Welcome to ECS 189C!

- **Listed Title:** Special Topics in Computer Science - Programming Languages and Compilers
- **CRN:** 41580
- **Units:** 4 (please change this in schedule builder!)
- **Flyer:** see [here](https://ucdavis.box.com/s/n4zd9b8wkc2thzcmjld5zqc7wfkn5pj1)
- **Instructor:** Caleb Stanford
- **TA:** Jason Yoo
- **Lectures:** Tuesdays and Thursdays, 10:30-11:50am in [Shields Library](https://campusmap.ucdavis.edu/?b=114) room 167
- **Final exam:** Friday, March 20, 10:30am-12:30pm. Please note that this is not in schedulebuilder! But it is the correct time for our class slot. If there are any unexpected changes to the schedule, then we will do the final exam in class.

## Lectures

I often lecture via live coding. I will post the code and lecture materials in this repository.
To follow along with the lectures, clone the repository:
```shell
git clone git@github.com:DavisPL-Teaching/189.git
```

If you make changes to the code after each lecture, you will need to discard them before pulling again.
For example, you can run:
```shell
git stash
git pull
```

### Lecture Recordings and Zoom

If you miss class, you can make up the lectures (and class polls) at any time
prior to the last day of class.
All lectures will be broadcast and recorded on Zoom.
However, this is a best-effort process, so please keep in mind that occasional technical
difficulties are possible (e.g., lost video recording, poor audio).
Zoom recordings will be made available on Canvas.


## Course Description

What does it mean for software to be correct?

In this upper-level undergraduate course, we will explore the principles and practices behind building software that functions as its intended. Through a survey of topics, including model-based verifiers, program verification tools, and advanced type systems, students will gain hands-on experience with writing program models and program specifications using tools used in industry at companies like Amazon and Microsoft.

### Prerequisites

This course is ideal for mid to upper-level undergraduate computer science majors.
While there are no official prerequisites, the following are unofficial requirements:

- A basic programming background (for example, the ability to write a program like [FizzBuzz](https://www.hackerrank.com/challenges/fizzbuzz/problem)) will be expected. (ECS 36A/36B/36C)
- Some familiarity with discrete mathematics or mathematical proofs (e.g. ECS 20) will be helpful, but not required.
- Some background in formal logic (like PHIL 12 or PHIL 112) is helpful, but not required.

### Learning Objectives

By the end of the course, students will be able to:

1. Understand the concept of software correctness and its importance.
2. Use random testing tools like Hypothesis for software testing.
3. Use model-based verifiers like Z3 for software analysis.
4. Apply program verification tools such as Dafny to ensure the correctness of software.
5. Explore advanced topics in software correctness, including advanced type systems and concurrency.

## Schedule

See `schedule.md`.

## Grade Breakdown

Your grade is evaluated based on:

- **Participation (10%):** via in-class polls
- **Homeworks (20%):** about 5 assignments planned (due bi-weekly), plus homework 0
- **Midterm (30%)**: covering the first half of the course
- **Final Exam (40%):** covering all topics covered in the course.

### Attendance and Participation

To encourage class attendance, there are in-class polls that are worth a small amount of credit.
However, if you miss class, you may make up the polls
by watching the lectures and filling out your responses offline.
Polls may be made up at any time prior to the last day of class.

The discussion section is recommended, but not mandatory.
It will be led by the TA and will also be recorded for those who cannot attend.

### Homeworks

Homeworks will consist of programming assignments designed to bring together concepts we learned in class
and to give you practice using all of the tools we cover.
I plan to assign about 3 homeworks, plus homework 0, which is designed to help you install the relevant software for the course.

**Important: your code must run to get credit!**
Frequently running and testing your code during development is an essential part of computer programming that can never be skipped.
You must run Python on your code before each submission to ensure that it works.
The graders will not be able to debug submissions, and code that does not run may receive a 0 or at most 50% of partial credit.

Homeworks will be graded primarily for correctness and completion.
There will also be a small number of points reserved for code quality - at most 10% of each assignment.
These points will consider: does you program exhibit high code quality standards?
Is it readable, shareable, well-documented, well-commented, logically separated into modules and functions, and reasonably efficient?
Are your free response answers thoughtful?
We will be using Gradescope for homework submissions and grading.

### Exams

There will be a midterm and a final exam.
Exams are closed-book, but you may bring a single-sided cheat sheet to each exam.
Exams will be graded on Gradescope.

I reserve the right to curve exams (this can only help you). That means, for example, if 100 points are possible, it may be entered as out of a smaller number of points like 95 or 85 for the purposes of calculating your grade, if the average score of the class was low or if there were unexpectedly difficult questions.

### Final Grade

For the final (letter) grade, the following are minimum cutoffs. That is, if your grade is above the given percentage, you will definitely receive at least the given grade. However, I reserve the right to lower the cutoffs (i.e. you might get a better grade than what the table says).
I will use this to help students who may be on the boundary between two grades at the end of the quarter.

| Percentage | Minimum Grade |
| --- | --- |
| 93 | A  |
| 90 | A- |
| 87 | B+ |
| 83 | B  |
| 80 | B- |
| 77 | C+ |
| 73 | C  |
| 70 | C- |
| 67 | D+ |
| 63 | D  |
| 60 | D- |

## Policies

### AI Policy

AI collaboration is allowed for homework assignments.
I encourage you to use AI in a way that is helpful to you, and to use caution that your use of AI is aiding (and not preventing) your own understanding of the material and critical thinking skills.
Exams are held in-class and closed-book.
Please see also [Prof. Jason Lowe-Power's advice here](https://jlpteaching.github.io/comparch/syllabus/#using-generative-ai-tools).

### Collaboration Policy and Academic Integrity

This class will encourage collaboration; however, each person should complete their own version of the assignment. **You should not directly copy code from someone else, even within your study group,** but you can receive help and give help on individual parts of an assignment.
In a real software development or data scientist job, it is common to seek and get help; this class will be no different!

You may work on homework assignments in groups of up to 3 people, as long as everyone is working on their own copy of the code. If you do this, please list the names of your collaborators at the top of your submission.

Here are some examples of good (allowed) collaboration:

- Sharing of resources
- Sharing of inspiration
- Sharing questions about the assignment on Piazza
- Helping out classmates on Piazza
- Collaboration at a low level (E.g., hey, what's the syntax for X, again? Why does this code print Y?)
- Collaboration at a high level (Why did they tell us to do this in that way?)
- As in most CS courses, the internet is your friend!

And here are examples of disallowed collaboration:

- Sharing large amounts of code with others within your group or others in the course.
- Sharing the exact solution to a specific mid-level programming problem.
- Asking a stranger to finish your work for you or copying and pasting what you find online for submission.

In other words, please use common sense!
This course strictly follows the [UC Davis Code of Academic Integrity](https://ossja.ucdavis.edu/academic-integrity).

### Late Policy

In-class participation points (polls) can be made up at any point during the quarter (prior to the last day of class), by submitting the Google form link. The forms will remain open and can be found by viewing the lecture recording or lecture notes for that day.
I will not be able to provide a consolidate list of the form links, as their purpose is to encourage you to attend and
watch the lectures.

Homeworks will generally be due at 11:59pm on the due date.
**I cannot guarantee that late homeworks will be graded.**
However, I encourage you to update your assignments even after the deadline -- Gradescope will allow you to upload late work up to a few days after the assignment deadline.
At grading time, we may choose to grade the more recent version at our discretion.

### Job Scams

Communication from the instructor will only be sent through official UC Davis email addresses and channels. Please be vigilant of job scams impersonating faculty members. For more information, visit [UC Davis Job Scams Prevention](https://careercenter.ucdavis.edu/job-and-internship-search/job-scams).

You can view and report job scam emails at the [Phish Bowl](https://phishbowl.ucdavis.edu/).

### Be Nice!

Finally: **please be kind to each other!**
UC Davis has [policies against harassment and discrimination](https://hr.ucdavis.edu/departments/elr/preventing-discrimination-harassment).
Be inclusive of your classmates in group study, in group work, and in your questions and answers in class.
If you need to, you may reach me by email to report an issue with a classmate.

## Contact and Office Hours

Please use the Piazza for questions related to course material.
If you send me an email, I will most likely respond to post your question on Piazza :)
Some Piazza guidelines:

* Please ask all questions publicly, with only one exception: if your post contains a large snippet of code then make it private.

* I encourage you to ask anonymously if you feel more comfortable.

The instructor and TAs will be available during office hours for additional support on course material and assignments. The schedule of office hours will be posted in a pinned note on Piazza.

If you have a question that is more sensitive or unrelated to the course, please email me (at `cdstanford` `ucdavis` `edu`).
